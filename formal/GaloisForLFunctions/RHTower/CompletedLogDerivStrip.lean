import GaloisForLFunctions.RHTower.SeamSuspensionTrace
import GaloisForLFunctions.RHTower.EdgeEventSynthesis

/-!
# The completed-zeta logarithmic derivative splits on the critical strip

On the open critical strip `0 < Re s < 1` the archimedean factor `archFactor` is nonvanishing
(`archFactor_ne_zero_strip`) and both it and `riemannZeta` are differentiable, so the logarithmic
derivative of the completed zeta `archFactor · riemannZeta` splits additively wherever
`riemannZeta s ≠ 0` — the only genuine side-condition left (the zeros are exactly what the seam
program locates).
-/

open Complex

namespace RHTower

/-- **The completed-zeta log-derivative splits on the strip.**  For `0 < Re s < 1` with
`riemannZeta s ≠ 0`, `logDeriv (archFactor · riemannZeta) s = logDeriv archFactor s + logDeriv
riemannZeta s`.  The archimedean nonvanishing (`archFactor_ne_zero_strip`) and the zeta
differentiability (`differentiableAt_riemannZeta`, `s ≠ 1` on the strip) are discharged, leaving
`riemannZeta s ≠ 0` as the sole hypothesis. -/
theorem logDeriv_completed_split_strip {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = logDeriv archFactor s + logDeriv riemannZeta s :=
  logDeriv_completed_split (archFactor_ne_zero_strip hstrip) hz
    (hasDerivAt_archFactor_of_re_pos hstrip.1).differentiableAt
    (differentiableAt_riemannZeta (fun h => by rw [h] at hstrip; norm_num at hstrip))

end RHTower
