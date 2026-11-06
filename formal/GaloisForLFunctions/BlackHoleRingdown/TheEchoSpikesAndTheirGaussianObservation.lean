import GaloisForLFunctions.BlackHoleRingdown.TheEchoTrainOfTheCusp

/-!
# Echo singularities and their Gaussian observation

Each arithmetic echo contributes a positive inverse-square-root spike. Since arrival times are
unbounded, subtracting any exponential mean still leaves arbitrarily late violations of every
pointwise exponential bound. This obstruction is independent of zeta zero locations.

The surviving estimate is an integrable one: every Laplace weight beyond `1/2` controls the echo
mass. Gaussian observation is therefore absolutely convergent and has an explicit global
majorant obtained by completing the square. Sharp decay after mean subtraction remains open.
-/

open Filter Topology Set MeasureTheory
noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown

theorem echoWeight_nonneg (c : ℕ) : 0 ≤ echoWeight c := by
  unfold echoWeight
  positivity

theorem echoWeight_pos {c : ℕ} (hc : 0 < c) : 0 < echoWeight c := by
  unfold echoWeight
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hc) (by exact_mod_cast hc)

theorem bounceKernel_pos {v : ℝ} (hv : 0 < v) : 0 < bounceKernel v := by
  apply Real.rpow_pos_of_pos
  have he : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem echoTerm_nonneg (c : ℕ) (τ : ℝ) : 0 ≤ echoTerm c τ := by
  unfold echoTerm
  split_ifs with h
  · exact mul_nonneg (echoWeight_nonneg c) (bounceKernel_pos (by linarith)).le
  · exact le_rfl

/-- Only denominators below `exp(τ/2)` can have arrived by time `τ`. -/
theorem echoTerm_eq_zero_of_exp_le {c : ℕ} {τ : ℝ}
    (hc : 0 < c) (hτ : Real.exp (τ / 2) ≤ c) : echoTerm c τ = 0 := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hlog : τ / 2 ≤ Real.log c := by
    exact not_lt.mp (fun h => (not_lt_of_ge hτ) ((Real.log_lt_iff_lt_exp hcR).mp h))
  rw [echoTerm, if_neg]
  unfold echoDelay
  linarith

/-- The echo train is a finite sum at each time, including at arrival times. -/
theorem echoTerm_hasFiniteSupport (τ : ℝ) :
    (Function.support (fun c : ℕ => echoTerm c τ)).Finite := by
  classical
  apply (Finset.finite_toSet (Finset.range (⌈Real.exp (τ / 2)⌉₊ + 1))).subset
  intro c hc
  have hn : echoTerm c τ ≠ 0 := hc
  have hcpos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := by omega
    subst c
    simp [echoTerm, echoWeight] at hn
  have hbound : (c : ℝ) < Real.exp (τ / 2) := by
    by_contra h
    exact hn (echoTerm_eq_zero_of_exp_le hcpos (le_of_not_gt h))
  have hceil : (c : ℝ) ≤ (⌈Real.exp (τ / 2)⌉₊ : ℝ) :=
    hbound.le.trans (Nat.le_ceil _)
  have hnat : c ≤ ⌈Real.exp (τ / 2)⌉₊ := by exact_mod_cast hceil
  simpa only [Finset.mem_coe, Finset.mem_range] using Nat.lt_succ_of_le hnat

theorem summable_echoTerm (τ : ℝ) : Summable (fun c : ℕ => echoTerm c τ) :=
  summable_of_hasFiniteSupport (echoTerm_hasFiniteSupport τ)

theorem echoTerm_le_echoKernel (c : ℕ) (τ : ℝ) : echoTerm c τ ≤ echoKernel τ := by
  exact (summable_echoTerm τ).le_tsum c (fun b _ => echoTerm_nonneg b τ)

theorem echoKernel_nonneg (τ : ℝ) : 0 ≤ echoKernel τ :=
  tsum_nonneg (fun c => echoTerm_nonneg c τ)

/-- The convergent Laplace transform is nonzero, hence its integrand is genuinely integrable. -/
theorem integrable_cexp_mul_echoKernel {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => Complex.exp (-w * (τ : ℂ)) * (echoKernel τ : ℂ)) := by
  have hne (s : ℂ) (hs : 1 < s.re) : completedRiemannZeta s ≠ 0 := by
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    intro hz
    apply riemannZeta_ne_zero_of_one_le_re hs.le
    rw [riemannZeta_def_of_ne_zero hs0, hz, zero_div]
  have hnum : completedRiemannZeta (2 * w) ≠ 0 := by
    apply hne
    norm_num
    linarith
  have hden : completedRiemannZeta (2 * w + 1) ≠ 0 := by
    apply hne
    norm_num
    linarith
  by_contra h
  have hi := integral_cexp_mul_echoKernel_eq_completed hw
  rw [integral_undef h] at hi
  exact (div_ne_zero hnum hden) hi.symm

/-- Every exponential weight beyond the half-line controls the absolute echo mass. -/
theorem integrable_exp_mul_echoKernel {a : ℝ} (ha : 1 / 2 < a) :
    Integrable (fun τ : ℝ => Real.exp (-a * τ) * echoKernel τ) := by
  have hi := (integrable_cexp_mul_echoKernel (w := (a : ℂ)) ha).re
  simpa only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.ofReal_re] using hi

theorem integrable_exp_neg_mul_echoKernel :
    Integrable (fun τ : ℝ => Real.exp (-τ) * echoKernel τ) := by
  simpa using integrable_exp_mul_echoKernel (a := 1) (by norm_num)

/-- The universal square-root lower profile at every positive echo delay. -/
theorem rpow_neg_half_le_bounceKernel {v : ℝ} (hv : 0 < v) :
    v ^ (-(1 / 2) : ℝ) ≤ bounceKernel v := by
  have he : Real.exp (-v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-v) := by linarith
  have hle : 1 - Real.exp (-v) ≤ v := by linarith [Real.add_one_le_exp (-v)]
  exact Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)

theorem echoKernel_squareRoot_lower (c : ℕ) {v : ℝ} (hv : 0 < v) :
    echoWeight c * v ^ (-(1 / 2) : ℝ) ≤ echoKernel (echoDelay c + v) := by
  calc
    echoWeight c * v ^ (-(1 / 2) : ℝ) ≤ echoWeight c * bounceKernel v :=
      mul_le_mul_of_nonneg_left (rpow_neg_half_le_bounceKernel hv) (echoWeight_nonneg c)
    _ = echoTerm c (echoDelay c + v) := by
      rw [echoTerm, if_pos (by linarith), add_sub_cancel_left]
    _ ≤ echoKernel (echoDelay c + v) := echoTerm_le_echoKernel _ _

/-- Every nonzero echo produces an unbounded right-hand spike in the full train. -/
theorem echoKernel_tendsto_atTop_at_echo {c : ℕ} (hc : 0 < c) :
    Tendsto (fun v : ℝ => echoKernel (echoDelay c + v)) (𝓝[>] 0) atTop := by
  have hpow := tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-(1 / 2) : ℝ) < 0)
  have hweight := Filter.Tendsto.const_mul_atTop (echoWeight_pos hc) hpow
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_ hweight
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact echoKernel_squareRoot_lower c hv

/-- No bounded pointwise estimate can cover even one full right neighborhood of an echo. -/
theorem exists_echoKernel_gt {c : ℕ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∃ v : ℝ, 0 < v ∧ v < ε ∧ M < echoKernel (echoDelay c + v) := by
  have hlarge := (echoKernel_tendsto_atTop_at_echo hc).eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ v : ℝ in 𝓝[>] 0, v < ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  exact (hlarge.and (self_mem_nhdsWithin.and hsmall)).exists.imp
    (fun v h => ⟨h.2.1, h.2.2, h.1⟩)

/-- Removing an exponential mean cannot give a global pointwise exponential remainder bound:
arbitrarily late echo arrivals violate every such bound. -/
theorem echoKernel_sub_mean_exceeds_every_exponential (A B b T : ℝ) :
    ∃ τ : ℝ, T < τ ∧ echoKernel τ - A * Real.exp (τ / 2) > B * Real.exp (b * τ) := by
  obtain ⟨c, hc⟩ := exists_nat_gt (Real.exp (T / 2))
  have hcR : (0 : ℝ) < c := (Real.exp_pos _).trans hc
  have hcN : 0 < c := by exact_mod_cast hcR
  have hdelay : T < echoDelay c := by
    have hl : T / 2 < Real.log c := by
      rw [← Real.exp_lt_exp, Real.exp_log hcR]
      exact hc
    unfold echoDelay
    linarith
  let U := echoDelay c + 1
  let M := |A| * Real.exp (U / 2) + |B| * Real.exp (|b| * U)
  obtain ⟨v, hv, hv1, hbig⟩ := exists_echoKernel_gt hcN (by norm_num : (0 : ℝ) < 1) M
  let τ := echoDelay c + v
  have hτ0 : 0 ≤ τ := by dsimp [τ]; linarith [echoDelay_nonneg c]
  have hτU : τ ≤ U := by dsimp [τ, U]; linarith
  have hA : A * Real.exp (τ / 2) ≤ |A| * Real.exp (U / 2) := by
    exact (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg A))
  have hbτ : b * τ ≤ |b| * U :=
    (mul_le_mul_of_nonneg_right (le_abs_self b) hτ0).trans
      (mul_le_mul_of_nonneg_left hτU (abs_nonneg b))
  have hB : B * Real.exp (b * τ) ≤ |B| * Real.exp (|b| * U) := by
    exact (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbτ) (abs_nonneg B))
  refine ⟨τ, by dsimp [τ]; linarith, ?_⟩
  change M < echoKernel τ at hbig
  dsimp only [M] at hbig
  linarith

/-- The Gaussian observation of the actual arithmetic echo source. -/
def gaussianEcho (σ t : ℝ) : ℝ :=
  ∫ τ : ℝ, Real.exp (-σ * (t - τ) ^ 2) * echoKernel τ

private theorem gaussian_weight_bound {σ : ℝ} (hσ : 0 < σ) (a t τ : ℝ) :
    Real.exp (-σ * (t - τ) ^ 2 + a * τ) ≤ Real.exp (a * t + a ^ 2 / (4 * σ)) := by
  apply Real.exp_le_exp.mpr
  have h : -σ * (t - τ) ^ 2 + a * τ - a * t ≤ a ^ 2 / (4 * σ) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * σ)).mpr
    nlinarith only [sq_nonneg (2 * σ * (τ - t) - a)]
  linarith

/-- Gaussian observation is absolutely convergent despite all echo singularities. -/
theorem integrable_gaussian_mul_echoKernel {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Integrable (fun τ : ℝ => Real.exp (-σ * (t - τ) ^ 2) * echoKernel τ) := by
  have hf : Continuous (fun τ : ℝ => Real.exp (-σ * (t - τ) ^ 2 + τ)) := by fun_prop
  have hi := integrable_exp_neg_mul_echoKernel.bdd_mul hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun τ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa using gaussian_weight_bound hσ 1 t τ))
  convert hi using 1
  funext τ
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A finite global majorant for every Gaussian observation. -/
theorem gaussianEcho_le {σ a : ℝ} (hσ : 0 < σ) (ha : 1 / 2 < a) (t : ℝ) :
    gaussianEcho σ t ≤ Real.exp (a * t + a ^ 2 / (4 * σ)) *
      ∫ τ : ℝ, Real.exp (-a * τ) * echoKernel τ := by
  rw [gaussianEcho, ← integral_const_mul]
  apply integral_mono (integrable_gaussian_mul_echoKernel hσ t)
    ((integrable_exp_mul_echoKernel ha).const_mul _)
  intro τ
  have h := mul_le_mul_of_nonneg_right (gaussian_weight_bound hσ a t τ)
    (mul_nonneg (Real.exp_pos (-a * τ)).le (echoKernel_nonneg τ))
  convert h using 1
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

#print axioms echoKernel_sub_mean_exceeds_every_exponential
#print axioms integrable_gaussian_mul_echoKernel
#print axioms gaussianEcho_le

end GaloisForLFunctions.BlackHoleRingdown
