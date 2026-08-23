import GaloisForLFunctions.RHTower.FriableMomentMellin
import GaloisForLFunctions.RHTower.FriableMomentBellEvaluation
import GaloisForLFunctions.RHTower.FriableMomentZetaJet
import GaloisForLFunctions.RHTower.FriableMomentPolygammaJet

/-!
# The friable log-moment ladder lands in a fixed finite-dimensional period space

The normalized friable log-moments

```text
M_j^{(T)} = (∫_0^∞ x^j (log x)^T dμ_S) / (j! ζ_S(j+1))
```

are exactly the normalized `T`-jets of `Γ ζ_S` at `j+1`.  The Bell transfer turns that jet into a
rational polynomial in the jet of `logDeriv (Γ ζ_S) = ψ + ζ_S'/ζ_S`, whose `i`-th coordinate lies
in the weight-`(i+1)` period layer.  Hence every `M_j^{(T)}` lies in the single finite-dimensional
weight-`T` layer `periodFilt S T`.
-/

open Filter MeasureTheory Set GaloisForLFunctions

open scoped Topology

namespace RHTower

noncomputable section

variable {k : ℕ}

theorem flux_ne_one_of_re_pos {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) * (p : ℂ) ^ (-s) ≠ 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hp
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = ((p : ℝ)) ^ (-s.re) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [Complex.neg_re]
  intro hcon
  rw [one_mul] at hcon
  have h1 : ‖(p : ℂ) ^ (-s)‖ = 1 := by rw [hcon, norm_one]
  rw [hnorm] at h1
  have hlt : ((p : ℝ)) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

/-- The friable Mellin datum `F(s) = Γ(s) ζ_S(s)`. -/
def friableMellinDatum (p : Fin k → ℕ) (s : ℂ) : ℂ :=
  Complex.Gamma s * eulerProductL p 1 s

theorem friableMellinDatum_ne_zero {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {s : ℂ} (hs : 0 < s.re) :
    friableMellinDatum p s ≠ 0 := by
  have hΓ : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    rw [hm] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact mul_ne_zero hΓ (eulerProductL_ne_zero fun i => flux_ne_one_of_re_pos (hp i) hs)

theorem analyticAt_friableMellinDatum {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ (friableMellinDatum p) s := by
  have hp0 : ∀ i, 0 < p i := fun i => by have := hp i; omega
  exact (HTGeometry.analyticAt_Gamma_of_re_pos hs).mul
    (analyticAt_eulerProductL hp0 1 fun i => flux_ne_one_of_re_pos (hp i) hs)

theorem logDeriv_friableMellinDatum {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {s : ℂ} (hs : 0 < s.re) :
    (fun w => deriv (friableMellinDatum p) w / friableMellinDatum p w) s
      = Complex.digamma s
        + (fun w => deriv (eulerProductL p 1) w / eulerProductL p 1 w) s := by
  have hp0 : ∀ i, 0 < p i := fun i => by have := hp i; omega
  have hdom : ∀ i, (1 : Fin k → ℂ) i * (p i : ℂ) ^ (-s) ≠ 1 := fun i => by
    rw [Pi.one_apply]
    exact flux_ne_one_of_re_pos (hp i) hs
  have hΓ : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    rw [hm] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hζ : eulerProductL p 1 s ≠ 0 := eulerProductL_ne_zero hdom
  have hdΓ : DifferentiableAt ℂ Complex.Gamma s :=
    (HTGeometry.analyticAt_Gamma_of_re_pos hs).differentiableAt
  have hdζ : DifferentiableAt ℂ (eulerProductL p 1) s := differentiableAt_eulerProductL hp0 1 hdom
  have h := logDeriv_mul s hΓ hζ hdΓ hdζ
  have hfun : friableMellinDatum p = fun z : ℂ => Complex.Gamma z * eulerProductL p 1 z := rfl
  rw [hfun]
  simpa [logDeriv_apply, Complex.digamma, logDeriv] using h

theorem iteratedDeriv_logDeriv_friableMellinDatum_mem {S : Finset ℕ} {p : Fin k → ℕ}
    (hpS : ∀ i, p i ∈ S) (hp2 : ∀ i, 2 ≤ p i) (i j : ℕ) :
    iteratedDeriv i (fun w => deriv (friableMellinDatum p) w / friableMellinDatum p w)
        ((j : ℂ) + 1) ∈ periodFilt S (i + 1) := by
  have hp0 : ∀ t, 0 < p t := fun t => by have := hp2 t; omega
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((j : ℂ) + 1) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < ((j : ℂ) + 1).re
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hev : (fun w => deriv (friableMellinDatum p) w / friableMellinDatum p w)
      =ᶠ[nhds ((j : ℂ) + 1)] (Complex.digamma
        + fun w => deriv (eulerProductL p 1) w / eulerProductL p 1 w) := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact logDeriv_friableMellinDatum hp2 hz
  rw [hev.iteratedDeriv_eq]
  have hoff : ∀ q : ℕ, ((j : ℂ) + 1) ≠ -(q : ℂ) := by
    intro q hq
    have := congrArg Complex.re hq
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.neg_re] at this
    have h1 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h2 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hcd1 : ContDiffAt ℂ (i : ℕ∞) Complex.digamma ((j : ℂ) + 1) := by
    have h := GaloisForLFunctions.analyticAt_logDeriv_Gamma ((j : ℂ) + 1) hoff
    exact (h.contDiffAt).of_le le_top
  have hcd2 : ContDiffAt ℂ (i : ℕ∞)
      (fun w => deriv (eulerProductL p 1) w / eulerProductL p 1 w) ((j : ℂ) + 1) := by
    have hdom : ∀ t, (1 : Fin k → ℂ) t * (p t : ℂ) ^ (-((j : ℂ) + 1)) ≠ 1 := fun t => by
      rw [Pi.one_apply]
      exact flux_ne_one_of_re_pos (hp2 t) hmem
    have han : AnalyticAt ℂ (eulerProductL p 1) ((j : ℂ) + 1) :=
      analyticAt_eulerProductL hp0 1 hdom
    have h := han.deriv.div han (eulerProductL_ne_zero hdom)
    exact (h.contDiffAt).of_le le_top
  rw [iteratedDeriv_add hcd1 hcd2]
  refine Submodule.add_mem _ (iteratedDeriv_digamma_mem_periodFilt S i j) ?_
  rw [iteratedDeriv_logDeriv_eulerProductL hp0 1 i
    (fun t => by rw [Pi.one_apply]; exact flux_ne_one_of_re_pos (hp2 t) hmem)]
  refine Submodule.neg_mem _ ?_
  rw [eulerFluxJet]
  refine Submodule.sum_mem _ fun t _ => ?_
  have hloc := localFluxJet_one_natSucc_mem_periodFilt (hpS t) (hp2 t) i j
  simpa using hloc

/-- **The normalized friable jet lands in the weight-`T` period layer.** -/
theorem friableJet_mem_periodFilt {S : Finset ℕ} {p : Fin k → ℕ}
    (hpS : ∀ i, p i ∈ S) (hp2 : ∀ i, 2 ≤ p i) (T j : ℕ) :
    iteratedDeriv T (friableMellinDatum p) ((j : ℂ) + 1) / friableMellinDatum p ((j : ℂ) + 1)
      ∈ periodFilt S T := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((j : ℂ) + 1) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < ((j : ℂ) + 1).re
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hfan : ∀ z ∈ {z : ℂ | 0 < z.re}, AnalyticAt ℂ (friableMellinDatum p) z := fun z hz =>
    analyticAt_friableMellinDatum hp2 hz
  have hfne : ∀ z ∈ {z : ℂ | 0 < z.re}, friableMellinDatum p z ≠ 0 := fun z hz =>
    friableMellinDatum_ne_zero hp2 hz
  have hbell := iteratedDeriv_eq_bellCore_generic hopen hfan hfne T hmem
  have hzne : friableMellinDatum p ((j : ℂ) + 1) ≠ 0 := friableMellinDatum_ne_zero hp2 hmem
  rw [hbell, mul_comm, mul_div_assoc, div_self hzne, mul_one, ← map_bellCoreQ T]
  exact eval_mem_periodFilt (isWeightedHomogeneous_bellCoreQ T)
    fun i => iteratedDeriv_logDeriv_friableMellinDatum_mem hpS hp2 (i : ℕ) j

/-! ## The card's normalized log-moments -/

/-- The card's numerator `∫_0^∞ x^j (log x)^T dμ_S`. -/
def friableLogMomentIntegral (p : Fin k → ℕ) (T j : ℕ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ((x ^ j * (Real.log x) ^ T : ℝ) : ℂ) * friableDensity p x

theorem friableLogMomentIntegral_eq_jet {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) (T j : ℕ) :
    friableLogMomentIntegral p T j
      = iteratedDeriv T (friableMellinDatum p) ((j : ℂ) + 1) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((j : ℂ) + 1) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < ((j : ℂ) + 1).re
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hev : mellin (friableDensity p) =ᶠ[nhds ((j : ℂ) + 1)] friableMellinDatum p := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact mellin_friableDensity hp hz
  rw [← hev.iteratedDeriv_eq, iteratedDeriv_mellin (mellinRapid_friableDensity hp) T hmem,
    mellin, friableLogMomentIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hcpow : (x : ℂ) ^ (((j : ℂ) + 1) - 1) = ((x ^ j : ℝ) : ℂ) := by
    rw [show (((j : ℂ) + 1) - 1) = ((j : ℕ) : ℂ) by ring,
      ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hx0.le, Real.rpow_natCast]
  rw [hcpow, logWeighted, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, mul_assoc]

/-- The card's normalized friable log-moment `M_j^{(T)}`. -/
def friableLogMoment (p : Fin k → ℕ) (T j : ℕ) : ℂ :=
  friableLogMomentIntegral p T j / ((j.factorial : ℂ) * eulerProductL p 1 ((j : ℂ) + 1))

/-- **Theorem A.**  Every normalized friable log-moment of weight `T` lies in the single
finite-dimensional weight-`T` period layer. -/
theorem friableLogMoment_mem_periodFilt {S : Finset ℕ} {p : Fin k → ℕ}
    (hpS : ∀ i, p i ∈ S) (hp2 : ∀ i, 2 ≤ p i) (T j : ℕ) :
    friableLogMoment p T j ∈ periodFilt S T := by
  have hfac : friableMellinDatum p ((j : ℂ) + 1)
      = (j.factorial : ℂ) * eulerProductL p 1 ((j : ℂ) + 1) := by
    rw [friableMellinDatum, Complex.Gamma_nat_eq_factorial]
  rw [friableLogMoment, friableLogMomentIntegral_eq_jet hp2, ← hfac]
  exact friableJet_mem_periodFilt hpS hp2 T j

end

end RHTower
