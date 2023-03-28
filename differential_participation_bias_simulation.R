#############################################################
### Here are simulation codes written to understand the selection bias
### due to differential participate in obsrvational cohorts based on
### coefficients from the Canadian Community Health Survey cohort
### by Chen Chen
#############################################################

library(gfoRmula)
library(data.table)
library(Hmisc)
library(survival)
# library(survminer)
# library(RColorBrewer)
library(timereg)
library(msm)
library(MASS)
# library(ggplot2)
# library(gridExtra)

setwd("~/selection_bias")

indir <- "simulation"

## function for data simulation and analysis
#############################################################
selected.sim.interval.geo <- function(    ## for goegraphical factor driven mechanism
  seeds,  # starting seeds for simulation
  unqid,  # id for repetition
  n,  # sample size
  yr, # study period
  delta,  # simulation interval
  rural_coef, ## coefficients for rural
  x_coef, ## coefficients for exposure
  f_coef, ## coefficients for unmeasured risk factor of death
  h_coef, ## coefficients for hazard
  s_coef, ## coefficients for probability of being selected
  ana.yrs, ## interval of years to analyze
  washout, ## number of years to ignore in the beginning
  ana.yrs.w ## interval of years to analyze in washout
) {
  set.seed(seeds + unqid)
  ## Set up key values
  time <- seq(delta, yr, by=delta)    # time points to simulate
  
  ## time since cohort inception
  measure.interval <- seq(1, length(time), by=1)  ## observation intervals
  nS <- length(time)  ## number of time points to simulate
  
  ## simulate rural vs. urban
  rural <- 1 * (runif(n, 0, 1) <= rural_coef["mean"]) ## 55% of rural residence
  
  ## simulate exposure
  x.b <- msm:::rtnorm(n, mean = x_coef["base"] + rural_coef["r_x"] * rural, sd = 2.2, lower= 1.8) ## base PM affected by rural (not baseline)
  ## time fixed exposure
  x <- x.b %*% t(rep(1, nS))
  
  ## simulate frailty
  f.b <- 1 * (runif(n, 0, 1) <= f_coef["base"] + ## baseline probability of being frail is 0.7
                rural_coef["r_f"] * rural  + ## being rural would increase the probability of being frail
                x_coef["x_f"] * x[, 1] ## x_coef["x_s"] decides whether exposure directly affects frailty
  ) 
  f <- f.b %*% t(c(rep(1, f_coef["f_year"]), rep(0, nS-f_coef["f_year"])))
  
  # combine into a data set
  sim.dat <- as.data.frame(cbind(id = seq(1, n),  rural, f.b, x[, measure.interval]))
  names(sim.dat)[3:(4 + nS - 1)] <- c("frail", paste0("PM", measure.interval))
  
  ## create matrix for the intensity process for each interval
  hmat <- h_coef["base"] +
    rural_coef["r_h"] * rural + 
    f_coef["f_h"] * f +
    x_coef["x_h"] * x  
  beta0 <- min(hmat)
  if (beta0 < 0) {
    hmat <- hmat + abs(beta0)
  }
  pmat <- hmat*delta ## pmat approximates the probability of event within an interval
  # adding id column
  p.mat.org <- cbind(1:n, pmat)
  ## simulate event time based on Strohmaier et.al. 2015 (Stats in Med), Section 4.1
  sim.dat$actualtime <- rep(time[length(time)], n)
  p.mat <- p.mat.org
  for(t in (measure.interval[1]):length(time)) {
    p.vec <- p.mat[, (t+1)]
    E <- rep(0, length(p.vec))
    id <- rep(0, length(p.vec))
    for(j in 1:length(p.vec)) {
      id[j] <- p.mat[j, 1]
      E[j] <- sample(c(0,1), 1, prob=c(1-p.vec[j], p.vec[j]))
    }
    if(any(E==1)) {
      id.event <- id[E==1]
      sim.dat[sim.dat$id %in% id.event, "actualtime"] <- time[t]-0.01
      p.mat <- p.mat[E==0, ]
    }
  }
  sim.dat$event <- 1*(sim.dat$actualtime < yr)  
  
  ## simulate selection
  p.s <- 
    s_coef["base"] + ## baseline probability of participating is 0.7
    rural_coef["r_s"] * rural  + ## being rural would increase the probability of being selected by 0.1
    x_coef["x_s"] * x[, 1] + ## x_coef["x_s"] decides whether exposure directly affects selection
    f_coef["f_s"] * f[, 1] ## healthy people more likely to participate--based on hazard in the first year
  
  
  # use a cutpoint--more pronounced selection bias
  sim.dat$selected <- ifelse(p.s >= quantile(p.s, probs = s_coef["cut"]), 1, 0)
  
  # Reshaping data to suited format
  mydata <- reshape(sim.dat, paste0("PM", measure.interval),
                    times = 0:(yr-1),
                    direction="long", v.names="PM")
  
  # Ordering
  mydata <- mydata[order(mydata[,"id"], mydata[,"time"]), ]
  row.names(mydata) <- 1:nrow(mydata)
  mydata <- mydata[, c("id", "rural", 
                       "frail",
                       "PM", "actualtime", "event", 
                       # "C", 
                       "time", "selected"
                       # , "selected.r", "selected.f"
  )]
  
  names(mydata)[7] <- "start"
  mydata$stopt <- mydata$start + 1 
  
  m.split <- split(mydata, mydata$id)
  
  hax <- function(df) {
    df$event <- 1*(df$actualtime <= df$stopt & sum(df$event) == nS )
    keep <- 1:min(c(which(df$event==1), nS))
    df <- df[keep, ]
  }
  
  m.split.hax <- lapply(m.split, hax)
  mydata.fin <- do.call("rbind", m.split.hax)
  
  mydata.fin <- mydata.fin[, c("id", "rural", 
                               "frail",
                               "PM", "event", 
                               "start","stopt", "selected", 
                               "actualtime")]

  ## original selected dataset
  interval.est <- numeric()
  for (yr_ in ana.yrs) {
    dt <- mydata.fin[mydata.fin$stopt<= yr_, ]
    
    ## aalen model
    aa.full <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt, id=dt$id, robust=0, n.sim = 1000)
    aa.b <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt[dt$selected==1, ], id=dt$id[dt$selected==1], n.sim = 1000)
    
    ## Cox model
    cox.full <- coxph(Surv(start, stopt, event) ~ PM, data=dt, ties = c("efron"), na.action = na.omit)
    cox.b <- coxph(Surv(start, stopt, event) ~ PM, data=dt[dt$selected==1, ], ties = c("efron"), na.action = na.omit)
    
    interval.est <- c(interval.est, aa.full$gamma[1], aa.b$gamma[1], aa.b$gamma[1] - aa.full$gamma[1], (aa.b$gamma[1] - aa.full$gamma[1])/aa.full$gamma[1],
                      summary(cox.full)$conf.int[1], summary(cox.b)$conf.int[1],  (summary(cox.b)$conf.int[1] - summary(cox.full)$conf.int[1])/summary(cox.full)$conf.int[1])
  }
  
  dt <- mydata.fin
  ## g-computation for observed cohort
  l.b <- glm(event ~ PM*as.factor(start), data=dt[dt$selected==1, ], family = "binomial")
  expsr <- "PM"
  temp <- dt[dt$selected==1 & dt$start==0, ]
  temp.new <- temp[rep(seq(1, nrow(temp)), each=nS), 1:6]
  temp.new$start <- rep(seq(0, nS-1), nrow(temp))
  temp.new$interv <- 0
  temp2 <- temp.new
  temp2[, expsr] <- ifelse(temp2[, expsr]>5, 5, temp2[, expsr])
  temp2$interv <- 2
  new <- rbind(temp.new, temp2)
  setDT(new)
  new$p.noevent <- 1- predict(l.b, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  out.b <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  out.b$riskdiff2[out.b$interv==2] <- (1-out.b$surv[out.b$interv==2]) - (1-out.b$surv[out.b$interv==0])
  
  ## g-computation for full--standardized to selected pop but association estimated with full dataset
  l.full <- glm(event ~ PM*as.factor(start), data=dt, family = "binomial")
  new$p.noevent <- 1- predict(l.full, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  out.full <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  out.full$riskdiff2[out.full$interv==2] <- (1-out.full$surv[out.full$interv==2]) - (1-out.full$surv[out.full$interv==0])
  
  
  ## engage washout period
  dt.w <- mydata.fin[mydata.fin$start >= washout,]
  dt.w$start <- dt.w$start - washout
  dt.w$stopt <- dt.w$stopt - washout
  dt.w$actualtime <- dt.w$actualtime - washout
  
  for (yr_ in ana.yrs.w) {
    dt <- dt.w[dt.w$stopt<= yr_, ]
    
    ## aalen model
    aa.full <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt, id=dt$id, robust=0, n.sim = 1000)
    aa.b <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt[dt$selected==1, ], id=dt$id[dt$selected==1], n.sim = 1000)
    
    ## Cox model
    cox.full <- coxph(Surv(start, stopt, event) ~ PM, data=dt, ties = c("efron"), na.action = na.omit)
    cox.b <- coxph(Surv(start, stopt, event) ~ PM, data=dt[dt$selected==1, ], ties = c("efron"), na.action = na.omit)
    summary(cox.b)$conf.int ## best achievable model, higher than below but lower pm_event than full
    
    interval.est <- c(interval.est, aa.full$gamma[1], aa.b$gamma[1], aa.b$gamma[1] - aa.full$gamma[1], (aa.b$gamma[1] - aa.full$gamma[1])/aa.full$gamma[1],
                      summary(cox.full)$conf.int[1], summary(cox.b)$conf.int[1],  (summary(cox.b)$conf.int[1] - summary(cox.full)$conf.int[1])/summary(cox.full)$conf.int[1])
  }
  
  dt <- dt.w
  ## g-computation for observed
  l.b <- glm(event ~ PM*as.factor(start), data=dt[dt$selected==1, ], family = "binomial")
  expsr <- "PM"
  temp <- dt[dt$selected==1 & dt$start==0, ]
  temp.new <- temp[rep(seq(1, nrow(temp)), each=nS-washout), 1:6]
  temp.new$start <- rep(seq(0, (nS-washout-1)), nrow(temp))
  temp.new$interv <- 0
  temp2 <- temp.new
  temp2[, expsr] <- ifelse(temp2[, expsr]>5, 5, temp2[, expsr])
  temp2$interv <- 2
  new <- rbind(temp.new, temp2)
  setDT(new)
  new$p.noevent <- 1- predict(l.b, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  outw.b <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  outw.b$riskdiff2[outw.b$interv==2] <- (1-outw.b$surv[outw.b$interv==2]) - (1-outw.b$surv[outw.b$interv==0])
  
  ## g-computation for full--standardized to selected pop but association estimated with full dataset
  l.full <- glm(event ~ PM*as.factor(start), data=dt, family = "binomial")
  new$p.noevent <- 1- predict(l.full, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  outw.full <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  outw.full$riskdiff2[outw.full$interv==2] <- (1-outw.full$surv[outw.full$interv==2]) - (1-outw.full$surv[outw.full$interv==0])
  
  
  return(
    c(
      interval.est,
      out.full$riskdiff2[out.full$interv==2],
      out.b$riskdiff2[out.b$interv==2],
      outw.full$riskdiff2[outw.full$interv==2],
      outw.b$riskdiff2[outw.b$interv==2]
    )
  )
  
}

select.sim.interval.frailty <- function ( ## for frailty driven mechanism
  seeds,  # starting seeds for simulation
  unqid,  # id for repetition
  n,  # sample size
  yr, # study period
  delta,  # simulation interval
  age_coef, ## coefficients for age
  rural_coef, ## coefficients for rural
  x_coef, ## coefficients for exposure
  u_coef, ## coefficients for unmeasured risk factor of death
  h_coef, ## coefficients for hazard
  s_coef, ## coefficients for probability of being selected
  ana.yrs, ## interval of years to analyze
  washout, ## number of years to ignore in the beginning
  ana.yrs.w ## interval of years to analyze in washout
) {
  set.seed(seeds + unqid)
  ## Set up key values
  time <- seq(delta, yr, by=delta)    # time points to simulate
  
  ## time since cohort inception
  measure.interval <- seq(1, length(time), by=1)  ## observation intervals
  nS <- length(time)  ## number of time points to simulate
  
  ## simulate age
  age0 <- round(msm:::rtnorm(n, mean = age_coef["mean"], sd = 20, lower = 25, upper = 80), digits=0)
  age <- matrix(rep(age0, nS), byrow=F, ncol=nS) + matrix(rep(rep(0:(yr - 1), each = 1/delta), n), byrow=T, nrow=n)
  
  ## simulate rural vs. urban
  rural <- 1 * (runif(n, 0, 1) <= rural_coef["mean"]) ## 55% of rural residence
  
  ## simulate exposure
  x.b <- msm:::rtnorm(n, mean = x_coef["base"] + rural_coef["r_x"] * rural, sd = 2.2, lower= 1.8) ## base PM affected by rural (not baseline)
  ## time fixed exposure
  x <- x.b %*% t(rep(1, nS))
  
  ## simulate U
  U.b <- 1 * (runif(n, 0, 1) <= u_coef["mean"]) ## 50% of population with frail gene
  U <- U.b %*% t(c(rep(1, u_coef["u_year"]), rep(0, nS-u_coef["u_year"])))
  
  # combine into a data set
  sim.dat <- as.data.frame(cbind(id = seq(1, n), age0, rural, U.b, x[, measure.interval]))
  names(sim.dat)[4:(5 + nS - 1)] <- c("U", paste0("PM", measure.interval))
  
  ## create matrix for the intensity process for each interval
  hmat <- h_coef["base"] +
    rural_coef["r_h"] * rural + 
    age_coef["a_h"] * age + 
    u_coef["u_h"] * U +
    x_coef["x_h"] * x  
  beta0 <- min(hmat)
  if (beta0 < 0) {
    hmat <- hmat + abs(beta0)
  }
  pmat <- hmat*delta ## pmat approximates the probability of event within an interval
  # adding id column
  p.mat.org <- cbind(1:n, pmat)
  ## simulate event time based on Strohmaier et.al. 2015 (Stats in Med), Section 4.1
  sim.dat$actualtime <- rep(time[length(time)], n)
  p.mat <- p.mat.org
  for(t in (measure.interval[1]):length(time)) {
    p.vec <- p.mat[, (t+1)]
    E <- rep(0, length(p.vec))
    id <- rep(0, length(p.vec))
    for(j in 1:length(p.vec)) {
      id[j] <- p.mat[j, 1]
      E[j] <- sample(c(0,1), 1, prob=c(1-p.vec[j], p.vec[j]))
    }
    if(any(E==1)) {
      id.event <- id[E==1]
      sim.dat[sim.dat$id %in% id.event, "actualtime"] <- time[t]-0.01
      p.mat <- p.mat[E==0, ]
    }
  }
  sim.dat$event <- 1*(sim.dat$actualtime < yr)  
  
  p.s <- ## better than above
    s_coef["base"] + ## baseline probability of participating is 0.7
    rural_coef["r_s"] * rural  + ## being rural would increase the probability of being selected by 0.1
    x_coef["x_s"] * x[, 1] + ## x_coef["x_s"] decides whether exposure directly affects selection
    h_coef["h_s"] * pmat[, 1]  ## healthy people more likely to participate--based on hazard in the first year
  
  
  # use a cutpoint--more pronounced selection bias
  sim.dat$selected <- ifelse(p.s >= quantile(p.s, probs = s_coef["cut"]), 1, 0)
  
  # Reshaping data to suited format
  mydata <- reshape(sim.dat, paste0("PM", measure.interval),
                    times = 0:(yr-1),
                    direction="long", v.names="PM")
  
  # Ordering
  mydata <- mydata[order(mydata[,"id"], mydata[,"time"]), ]
  row.names(mydata) <- 1:nrow(mydata)
  mydata <- mydata[, c("id", "age0", "rural", 
                       "U",
                       "PM", "actualtime", "event", 
                       "time", "selected"
  )]
  
  names(mydata)[8] <- "start"
  mydata$stopt <- mydata$start + 1 
  
  m.split <- split(mydata, mydata$id)
  
  hax <- function(df) {
    df$event <- 1*(df$actualtime <= df$stopt & sum(df$event) == nS )
    keep <- 1:min(c(which(df$event==1), nS))
    df <- df[keep, ]
  }
  
  m.split.hax <- lapply(m.split, hax)
  mydata.fin <- do.call("rbind", m.split.hax)
  
  mydata.fin <- mydata.fin[, c("id", "age0", "rural", 
                               "U",
                               "PM", "event", 
                               "start","stopt", "selected", 
                               "actualtime")]
  
  # original selected dataset
  interval.est <- numeric()
  for (yr_ in ana.yrs) {
    dt <- mydata.fin[mydata.fin$stopt<= yr_, ]
    
    ## aalen model
    aa.full <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt, id=dt$id, robust=0, n.sim = 1000)
    aa.b <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt[dt$selected==1, ], id=dt$id[dt$selected==1], n.sim = 1000)
    
    ## Cox model
    cox.full <- coxph(Surv(start, stopt, event) ~ PM, data=dt, ties = c("efron"), na.action = na.omit)
    cox.b <- coxph(Surv(start, stopt, event) ~ PM, data=dt[dt$selected==1, ], ties = c("efron"), na.action = na.omit)
    summary(cox.b)$conf.int ## best achievable model, higher than below but lower pm_event than full
    
    interval.est <- c(interval.est, aa.full$gamma[1], aa.b$gamma[1], aa.b$gamma[1] - aa.full$gamma[1], (aa.b$gamma[1] - aa.full$gamma[1])/aa.full$gamma[1],
                      summary(cox.full)$conf.int[1], summary(cox.b)$conf.int[1],  (summary(cox.b)$conf.int[1] - summary(cox.full)$conf.int[1])/summary(cox.full)$conf.int[1])
  }
  
  dt <- mydata.fin
  ## g-computation for observed
  l.b <- glm(event ~ PM*as.factor(start), data=dt[dt$selected==1, ], family = "binomial")
  expsr <- "PM"
  temp <- dt[dt$selected==1 & dt$start==0, ]
  temp.new <- temp[rep(seq(1, nrow(temp)), each=nS), 1:6]
  temp.new$start <- rep(seq(0, nS-1), nrow(temp))
  temp.new$interv <- 0
  temp2 <- temp.new
  temp2[, expsr] <- ifelse(temp2[, expsr]>5, 5, temp2[, expsr])
  temp2$interv <- 2
  new <- rbind(temp.new, temp2)
  setDT(new)
  new$p.noevent <- 1- predict(l.b, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  out.b <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  out.b$riskdiff2[out.b$interv==2] <- (1-out.b$surv[out.b$interv==2]) - (1-out.b$surv[out.b$interv==0])
  
  ## g-computation for full--standardized to selected pop but association estimated with full dataset
  l.full <- glm(event ~ PM*as.factor(start), data=dt, family = "binomial")
  new$p.noevent <- 1- predict(l.full, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  out.full <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  out.full$riskdiff2[out.full$interv==2] <- (1-out.full$surv[out.full$interv==2]) - (1-out.full$surv[out.full$interv==0])
  
  
  ## engage washout period
  dt.w <- mydata.fin[mydata.fin$start >= washout,]
  dt.w$age0 <- dt.w$age0 + washout
  dt.w$start <- dt.w$start - washout
  dt.w$stopt <- dt.w$stopt - washout
  dt.w$actualtime <- dt.w$actualtime - washout
  
  for (yr_ in ana.yrs.w) {
    dt <- dt.w[dt.w$stopt<= yr_, ]
    
    ## aalen model
    aa.full <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt, id=dt$id, robust=0, n.sim = 1000)
    aa.b <- aalen(Surv(start, stopt, event) ~ const(PM), data=dt[dt$selected==1, ], id=dt$id[dt$selected==1], n.sim = 1000)
    
    ## Cox model
    cox.full <- coxph(Surv(start, stopt, event) ~ PM, data=dt, ties = c("efron"), na.action = na.omit)
    cox.b <- coxph(Surv(start, stopt, event) ~ PM, data=dt[dt$selected==1, ], ties = c("efron"), na.action = na.omit)
    summary(cox.b)$conf.int ## best achievable model, higher than below but lower pm_event than full
    
    interval.est <- c(interval.est, aa.full$gamma[1], aa.b$gamma[1], aa.b$gamma[1] - aa.full$gamma[1], (aa.b$gamma[1] - aa.full$gamma[1])/aa.full$gamma[1],
                      summary(cox.full)$conf.int[1], summary(cox.b)$conf.int[1],  (summary(cox.b)$conf.int[1] - summary(cox.full)$conf.int[1])/summary(cox.full)$conf.int[1])
  }
  
  dt <- dt.w
  ## g-computation for observed
  l.b <- glm(event ~ PM*as.factor(start), data=dt[dt$selected==1, ], family = "binomial")
  expsr <- "PM"
  temp <- dt[dt$selected==1 & dt$start==0, ]
  temp.new <- temp[rep(seq(1, nrow(temp)), each=nS-washout), 1:6]
  temp.new$start <- rep(seq(0, (nS-washout-1)), nrow(temp))
  temp.new$interv <- 0
  temp2 <- temp.new
  temp2[, expsr] <- ifelse(temp2[, expsr]>5, 5, temp2[, expsr])
  temp2$interv <- 2
  new <- rbind(temp.new, temp2)
  setDT(new)
  new$p.noevent <- 1- predict(l.b, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  outw.b <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  outw.b$riskdiff2[outw.b$interv==2] <- (1-outw.b$surv[outw.b$interv==2]) - (1-outw.b$surv[outw.b$interv==0])
  
  ## g-computation for full--standardized to selected pop but association estimated with full dataset
  l.full <- glm(event ~ PM*as.factor(start), data=dt, family = "binomial")
  new$p.noevent <- 1- predict(l.full, new, type="response")
  new[, surv := cumprod(p.noevent), by = .(interv, id)]
  outw.full <- new[, lapply(.SD, mean), by = .(interv, start), .SDcols = c(expsr, "surv")]
  outw.full$riskdiff2[outw.full$interv==2] <- (1-outw.full$surv[outw.full$interv==2]) - (1-outw.full$surv[outw.full$interv==0])
  
  
  return(
    c(
      interval.est,
      out.full$riskdiff2[out.full$interv==2],
      out.b$riskdiff2[out.b$interv==2],
      outw.full$riskdiff2[outw.full$interv==2],
      outw.b$riskdiff2[outw.b$interv==2]
    )
  )
}
#############################################################


## Run simulations
n.rep <- 100
yr <- 10                            # study period: 10 years
n.size <- 100000			    # sample size, 10k takes 100s, 100k takes 35 mins
delta <- 1                       # simulation interval: 1 month = 1/12 year
washout <- 3  ## washout years dropped in analysis
ana.yrs <- c(yr, 5, 3)
ana.yrs.w <- c(yr-washout, 5, 3)
#############################################################
### Frailty driven mechanism
type <- "frail_intvs_real"
age_coef <- c(mean = 48, a_x = 0, a_h = 0)
rural_coef <- c(mean = 0.55, r_x = 0, r_h = 0, r_s = 0)
x_coef <- c(base = 7.4, x_h = 0.0002, x_s = 0) #exposure, x_coef["x_hs"] decides whether exposure affects selection through frailty (binary)
u_coef <- c(mean = 0.8, u_h = 0.003, u_year=3) #unmeasured risk factor for death--no affecting hazards after u_year year, min value 0, max value 10
h_coef <- c(base = 0.006, h_s = -10) #hazard for death
s_coef <- c(base = 0.7, cut = 0.3) #probability of being selected
## incorporate multiple analysis intervals
interv.est <- paste(c("aa.target", "aa.selected", "aa.dif", "aa.reldif", "cox.target", "cox.selected", "cox.reldif"), rep(c("all", 5, 3), each=7), sep=".")
dsets <- c("original", "washout")
all.ori <-  paste("gcomp", 1:yr, sep=".")
dsets.ori <- c("full_original", "selected_original")
all.w <-  paste("gcomp", 1:(yr-washout), sep=".")
dsets.w <- c("full_washout", "selected_washout")
nms <- c(
  paste(rep(dsets, each = length(interv.est)),
        interv.est, sep="_"),
  paste(rep(dsets.ori, each = length(all.ori)), 
        all.ori, sep="_"),
  paste(rep(dsets.w, each = length(all.w)), 
        all.w, sep="_")
)
## below for gcomp_frail
foo <- data.frame(repeatition = 1:n.rep, yr = yr, n.size = n.size, sim.coef = as.numeric(x_coef["x_h"]),
                  washout = washout, u.year = as.numeric(u_coef["u_year"]),
                  setNames(replicate(length(nms), NA, simplify = F), nms))
sim.start <- Sys.time()
for (id in 1:n.rep) {
  # id <- id + 100
  foo[id, 7:ncol(foo)] <- select.sim.interval.frailty(651, id, n.size, yr, delta, age_coef, rural_coef, x_coef, u_coef, h_coef, s_coef, ana.yrs, washout, ana.yrs.w)
  if (id%%10==0) cat("finished running simulation", id, "\n")
}
cat("simulation took", difftime(Sys.time(), sim.start, units = "s"), "\n")
write.csv(foo, file.path("results", paste0(type, "_", n.rep, "cohorts_", n.size, "size_", washout, "years.csv")), row.names = FALSE)


### geographical factor driven mechanism
type <- "rural_intvs_real"
rural_coef <- c(mean = 0.55, r_x = -6, r_f = 0, r_h = 0, r_s = 0.6)
x_coef <- c(base = 7.4, x_f = 0, x_h = 0.0002, x_s = 0) ## exposure
f_coef <- c(base = 0.5, f_h = 0.003, f_s = -0.45, f_year=3) ## frailty
h_coef <- c(base = 0.006) #hazard for death
s_coef <- c(base = 0.7, cut = 0.3) #probability of being selected
## incorporate multiple analysis intervals
interv.est <- paste(c("aa.target", "aa.selected", "aa.dif", "aa.reldif", "cox.target", "cox.selected", "cox.reldif"), rep(c("all", 5, 3), each=7), sep=".")
dsets <- c("original", "washout")
all.ori <-  paste("gcomp", 1:yr, sep=".")
dsets.ori <- c("full_original", "selected_original")
all.w <-  paste("gcomp", 1:(yr-washout), sep=".")
dsets.w <- c("full_washout", "selected_washout")
nms <- c(
  paste(rep(dsets, each = length(interv.est)),
        interv.est, sep="_"),
  paste(rep(dsets.ori, each = length(all.ori)), 
        all.ori, sep="_"),
  paste(rep(dsets.w, each = length(all.w)), 
        all.w, sep="_")
)
## below for no U rural-rural
foo <- data.frame(repeatition = 1:n.rep, yr = yr, n.size = n.size, sim.coef = as.numeric(x_coef["x_h"]),
                  washout = washout, f.year = as.numeric(f_coef["f_year"]),
                  setNames(replicate(length(nms), NA, simplify = F), nms))
sim.start <- Sys.time()
for (id in 1:n.rep) {
  # id <- id + 100
  foo[id, 7:ncol(foo)] <- selected.sim.interval.geo(825, id, n.size, yr, delta, rural_coef, x_coef, f_coef, h_coef, s_coef, ana.yrs, washout, ana.yrs.w)
  if (id%%10==0) cat("finished running simulation", id, "\n")
}
cat("simulation took", difftime(Sys.time(), sim.start, units = "s"), "\n")
write.csv(foo, file.path("results", paste0(type, "_", n.rep, "cohorts_", n.size, "size_", washout, "years.csv")), row.names = FALSE)
#############################################################
