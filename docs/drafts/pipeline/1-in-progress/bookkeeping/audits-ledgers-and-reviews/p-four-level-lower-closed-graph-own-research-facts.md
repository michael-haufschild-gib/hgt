# Route P four-level lower closed-graph: own research facts

- **LEAN FACT.** For every source-clock degree `n` and lower-half parameter `t > 0`, the literal
  prime-log theta coefficient is source-`ℓ²` with exact squared mass
  ```text
  4 log(p)^(2 n + 4) / p^(1 + 2 t).
  ```
  This is `norm_sq_primeLogThetaLowerClockCoefficient` and
  `memℓp_primeLogThetaLowerClockCoefficient`.

- **LEAN FACT.** The four reporters of degrees `0,1,2,3` form one linear map from
  `Graph(cl primeLogCriticalLaplaceSynthesis)` to `Fin 4 -> C`.  On every literal graph-core
  point, level `i` is exactly the denominator-free Wronskian representative
  `XiC(-i t)^(1+i) Q_i`; `primeLogThetaStripWronskianIterate_lowerFourLevelClosedGraphCore`
  retains all four Xi powers without division.

- **LEAN FACT.** Every labelled pair `(i,j)` has an exact mixed identity with distinct left and
  right Xi powers and its retained source cross term:
  `primeLogThetaStripWronskianIterate_lowerFourLevelMixedCore`.

- **WHOLE-ROUTE CONSEQUENCE.** The lower-half `Graph(cl A_*)` stage no longer loses its
  four-level filtration or its finite mixed labels.  This does not cross the real theta axis:
  literal real-axis reporters remain non-`ℓ²`.  Route P’s live hard gate is therefore the
  genuinely graph-relative real-axis/Calderón boundary morphism and its Xi escape pairing, not
  another finite-core clock identity.
