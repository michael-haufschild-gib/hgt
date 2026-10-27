import GaloisForLFunctions.BiarithmeticGaugeGeometry.LatticeSievedPostWidderAndLandauAnchor
import GaloisForLFunctions.BiarithmeticGaugeGeometry.ChiralDeformationAndNonRigidityOfHeightCoupledSystems
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.EMAnnulusSupply

/-!
# Rational Bochner Deformations of the Height-Coupled Euler Carrier

A **rational deformation** of the height-coupled carrier `ζ_γ(s) = ζ(s)² ζ(s + iγ) ζ(s − iγ)` is a
member `(F, Λ)` of `HeightCoupledSystem 2 1 1 γ` with `F = ζ_γ · R` on `Re s > 1` for a rational
multiplier `R(s) = ∏ᵢ (s − zᵢ)^{mᵢ}` (`mᵢ ∈ ℤ`). The outward splitting `W_β` and the off-critical
quartet contraction are both rational deformations. This module classifies all of them.

1. **The height-coupled lattice (`heightCoupledVonMangoldt`,
   `neg_logDeriv_heightCoupledF_eq_LSeries`).** `−ζ_γ'/ζ_γ = Σ Λ(n) |1 + n^{iγ}|² n^{−s}` is a
   Dirichlet series with nonnegative coefficients `Λ(n)(2 + 2 cos(γ log n))`.

2. **Polar data of the multiplier (`neg_logDeriv_rationalMultiplier`,
   `rationalMultiplier_eq_zpow_mul_cofactor`).** `−R'/R` is the polar sum with weight `−M(w)` at
   the net multiplicity `M(w) = Σ_{zᵢ = w} mᵢ`, and `R = (s − w)^{M(w)} · R_w` with `R_w(w) ≠ 0`.

3. **Classification (`rationalDeformation_real_anchor`).** By the lattice real anchor, the rightmost
   point `w₀` of nonzero net multiplicity forces a real pole `M(Re w₀) < 0` dominating the whole
   line `Re s = Re w₀`. The completion identity `Λ = Λ_γ · R` (identity theorem off the finite
   multiplier set) and pole forcing give `Λ_γ(Re w₀) = 0`, i.e. `ξ(Re w₀ + iγ) = 0`: **every
   nontrivial rational deformation is anchored at a zero of `ξ` on the horizontal line at height
   `γ`.**

4. **Rational rigidity (`rationalDeformation_rigid_of_xi_ne_zero_on_line`,
   `rationalDeformation_rigid_zero_height`).** At every height whose horizontal line carries no zero
   of `ξ` — in particular at `γ = 0`, unconditionally — every rational deformation is trivial:
   `F = ζ_γ` and `Λ = Λ_γ`. This is the positive survivor of the false two-sided `CoupledRigid`.

5. **Exact chiral descent (`rationalDeformation_central_descent`).** If `ξ` has no off-critical zero
   at ordinate `γ`, a nontrivial rational deformation has a central multiplier pole and
   `ord_{1/2} Λ + (−M(1/2)) = ord_{1/2} Λ_γ`: outward chirality is a theorem, not an example.

6. **The ceiling is a horizontal zero-free line (`rationalCentralVanishingCeiling_iff`,
   `riemannHypothesis_iff_forall_rationalCentralVanishingCeiling`).** For `γ ≠ 0`, the rational
   central ceiling holds iff `ξ` has no off-critical zero at ordinate `γ` (the quartet contraction is
   a rational multiplier raising the central order by `4`); hence RH is equivalent to the rational
   chiral ceiling at every height.
-/

open Complex Filter Topology Set Finset
open scoped ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry StripBochnerWeilForcing

/-! ## §1. The height-coupled lattice series -/

/-- Lattice coefficients `Λ(n) |1 + n^{iγ}|² = Λ(n)(2 + 2 cos(γ log n))` of `−ζ_γ'/ζ_γ`. -/
def heightCoupledVonMangoldt (γ : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (2 + 2 * Real.cos (γ * Real.log n))

theorem heightCoupledVonMangoldt_nonneg (γ : ℝ) (n : ℕ) : 0 ≤ heightCoupledVonMangoldt γ n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (by nlinarith [Real.neg_one_le_cos (γ * Real.log n)])

theorem abscissaOfAbsConv_heightCoupledVonMangoldt_le_one (γ : ℝ) :
    LSeries.abscissaOfAbsConv (fun n => (heightCoupledVonMangoldt γ n : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (y : ℂ)) (by simpa using hy)
  refine Summable.of_norm_bounded (hΛ.norm.mul_left 4) fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heightCoupledVonMangoldt_nonneg γ n),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      mul_div_assoc', div_le_div_iff_of_pos_right
        (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _)]
    unfold heightCoupledVonMangoldt
    nlinarith [Real.cos_le_one (γ * Real.log n),
      ArithmeticFunction.vonMangoldt_nonneg (n := n)]

/-- `n^{iγ} + n^{−iγ} = 2 cos(γ log n)` for `n ≥ 1`. -/
theorem natCast_cpow_mul_I_add_neg (n : ℕ) (hn : n ≠ 0) (γ : ℝ) :
    (n : ℂ) ^ ((γ : ℂ) * I) + ((n : ℂ) ^ ((γ : ℂ) * I))⁻¹ =
      ((2 * Real.cos (γ * Real.log n) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0,
    ← Complex.natCast_log]
  have h := Complex.two_cos ((γ * Real.log n : ℝ) : ℂ)
  rw [show ((2 * Real.cos (γ * Real.log n) : ℝ) : ℂ) =
      2 * Complex.cos ((γ * Real.log n : ℝ) : ℂ) by push_cast; rfl, h]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- **The height-coupled carrier is a nonnegative lattice series:**
`−ζ_γ'/ζ_γ(s) = Σ Λ(n)(2 + 2 cos(γ log n)) n^{−s}` on `Re s > 1`. -/
theorem neg_logDeriv_heightCoupledF_eq_LSeries (γ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (heightCoupledF riemannZeta γ) s =
      LSeries (fun n => (heightCoupledVonMangoldt γ n : ℂ)) s := by
  set c : ℂ := (γ : ℂ) * I with hc
  have hsp : 1 < (s + c).re := by simpa [hc] using hs
  have hsm : 1 < (s - c).re := by simpa [hc] using hs
  have hsm' : 1 < (s + -c).re := by simpa [sub_eq_add_neg] using hsm
  have hne : ∀ w : ℂ, 1 < w.re → w ≠ 1 := fun w hw h => by rw [h] at hw; simp at hw
  have hz : ∀ w : ℂ, 1 < w.re → riemannZeta w ≠ 0 := fun w hw =>
    riemannZeta_ne_zero_of_one_lt_re hw
  have hd : ∀ w : ℂ, 1 < w.re → DifferentiableAt ℂ riemannZeta w := fun w hw =>
    differentiableAt_riemannZeta (hne w hw)
  have hlogζ : ∀ w : ℂ, 1 < w.re →
      logDeriv riemannZeta w = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w := by
    intro w hw
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw, logDeriv_apply]
    ring
  have hshift : ∀ e : ℂ, 1 < (s + e).re →
      logDeriv (fun w => riemannZeta (w + e)) s = logDeriv riemannZeta (s + e) := by
    intro e he
    have h := logDeriv_comp (f := riemannZeta) (g := fun w => w + e) (x := s) (hd _ he)
      (by fun_prop)
    rw [show (riemannZeta ∘ fun w => w + e) = fun w => riemannZeta (w + e) from rfl] at h
    rw [h, deriv_add_const, deriv_id'', mul_one]
  have hsub : (fun w => riemannZeta (w - c)) = fun w => riemannZeta (w + -c) := by
    funext w; rw [sub_eq_add_neg]
  have hdp : DifferentiableAt ℂ (fun w => riemannZeta (w + c)) s :=
    (hd _ hsp).comp s (by fun_prop)
  have hdm : DifferentiableAt ℂ (fun w => riemannZeta (w - c)) s :=
    (hd _ hsm).comp s (by fun_prop)
  have hd2 : DifferentiableAt ℂ (fun w => riemannZeta w ^ 2) s := (hd _ hs).pow 2
  have hL : -logDeriv (heightCoupledF riemannZeta γ) s =
      2 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s +
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + c) +
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - c) := by
    have hF : heightCoupledF riemannZeta γ =
        fun w => riemannZeta w ^ 2 * riemannZeta (w + c) * riemannZeta (w - c) := rfl
    rw [hF, logDeriv_mul (f := fun w => riemannZeta w ^ 2 * riemannZeta (w + c))
        (g := fun w => riemannZeta (w - c)) s
        (mul_ne_zero (pow_ne_zero 2 (hz _ hs)) (hz _ hsp)) (hz _ hsm) (hd2.mul hdp) hdm,
      logDeriv_mul (f := fun w => riemannZeta w ^ 2) (g := fun w => riemannZeta (w + c)) s
        (pow_ne_zero 2 (hz _ hs)) (hz _ hsp) hd2 hdp,
      logDeriv_fun_pow (hd _ hs), hshift c hsp, hsub, hshift (-c) hsm', ← sub_eq_add_neg,
      hlogζ s hs, hlogζ _ hsp, hlogζ _ hsm]
    push_cast; ring
  have h1 := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h2 := ArithmeticFunction.LSeriesSummable_vonMangoldt hsp
  have h3 := ArithmeticFunction.LSeriesSummable_vonMangoldt hsm
  rw [hL, LSeries, LSeries, LSeries, LSeries, ← tsum_mul_left,
    ← (h1.mul_left 2).tsum_add h2, ← ((h1.mul_left 2).add h2).tsum_add h3]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow := natCast_cpow_mul_I_add_neg n hn γ
  rw [← hc] at hpow
  have hns : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
  have hnc : (n : ℂ) ^ c ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
  simp only [LSeries.term_of_ne_zero hn]
  rw [Complex.cpow_add _ _ hn0, sub_eq_add_neg, Complex.cpow_add _ _ hn0, Complex.cpow_neg,
    heightCoupledVonMangoldt,
    show ((ArithmeticFunction.vonMangoldt n * (2 + 2 * Real.cos (γ * Real.log n)) : ℝ) : ℂ) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (2 + ((2 * Real.cos (γ * Real.log n) : ℝ) : ℂ))
      by push_cast; ring, ← hpow]
  generalize (n : ℂ) ^ c = X at hnc ⊢
  generalize (n : ℂ) ^ s = Y at hns ⊢
  field_simp
  ring

/-! ## §2. Rational multipliers and their polar data -/

/-- Rational multiplier `R(s) = ∏ᵢ (s − zᵢ)^{mᵢ}` with integer exponents. -/
def rationalMultiplier {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (s - z i) ^ m i

/-- Net multiplicity `M(w) = Σ_{zᵢ = w} mᵢ` of a rational multiplier at `w`. -/
def netMultiplicity {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) (w : ℂ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i => z i = w), m i

/-- Polar weight of `−R'/R` at `w`: `−M(w)`. -/
def multiplierWeight {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) (w : ℂ) : ℝ :=
  -(netMultiplicity z m w : ℝ)

/-- Off-fibre cofactor `R_w(s) = ∏_{zᵢ ≠ w} (s − zᵢ)^{mᵢ}`. -/
def multiplierCofactor {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) (w s : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => z i ≠ w), (s - z i) ^ m i

theorem prod_zpow_eq_zpow_sum {ι : Type*} {x : ℂ} (hx : x ≠ 0) (s : Finset ι) (m : ι → ℤ) :
    ∏ i ∈ s, x ^ m i = x ^ (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hx]

theorem netMultiplicity_eq_zero_of_notMem {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) {w : ℂ}
    (hw : w ∉ Finset.univ.image z) : netMultiplicity z m w = 0 := by
  unfold netMultiplicity
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩) hw

/-- `R = (s − w)^{M(w)} · R_w` away from `w`. -/
theorem rationalMultiplier_eq_zpow_mul_cofactor {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ)
    {w s : ℂ} (hs : s ≠ w) :
    rationalMultiplier z m s = (s - w) ^ netMultiplicity z m w * multiplierCofactor z m w s := by
  unfold rationalMultiplier multiplierCofactor netMultiplicity
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => z i = w)]
  congr 1
  rw [← prod_zpow_eq_zpow_sum (sub_ne_zero.mpr hs)]
  exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

theorem analyticAt_sub_zpow (w : ℂ) (k : ℤ) {s : ℂ} (hs : s ≠ w) :
    AnalyticAt ℂ (fun x : ℂ => (x - w) ^ k) s :=
  (analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hs)

theorem rationalMultiplier_analyticAt {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) {s : ℂ}
    (hs : ∀ i, s ≠ z i) : AnalyticAt ℂ (rationalMultiplier z m) s := by
  have h := Finset.analyticAt_prod (f := fun i (x : ℂ) => (x - z i) ^ m i) (c := s) Finset.univ
    fun i _ => analyticAt_sub_zpow (z i) (m i) (hs i)
  have he : rationalMultiplier z m = ∏ i, fun x : ℂ => (x - z i) ^ m i := by
    funext x; simp [rationalMultiplier, Finset.prod_apply]
  rwa [he]

theorem multiplierCofactor_analyticAt {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) (w : ℂ) :
    AnalyticAt ℂ (multiplierCofactor z m w) w := by
  have h := Finset.analyticAt_prod (f := fun i (x : ℂ) => (x - z i) ^ m i) (c := w)
    (Finset.univ.filter fun i => z i ≠ w)
    fun i hi => analyticAt_sub_zpow (z i) (m i) (Finset.mem_filter.mp hi).2.symm
  have he : multiplierCofactor z m w =
      ∏ i ∈ Finset.univ.filter (fun i => z i ≠ w), fun x : ℂ => (x - z i) ^ m i := by
    funext x; simp [multiplierCofactor, Finset.prod_apply]
  rwa [he]

theorem multiplierCofactor_self_ne_zero {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) (w : ℂ) :
    multiplierCofactor z m w w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi =>
    zpow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_filter.mp hi).2.symm)

/-- **Polar data of the multiplier:** `−R'/R = Σ_w (−M(w))/(s − w)` off the multiplier points. -/
theorem neg_logDeriv_rationalMultiplier {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℤ) {s : ℂ}
    (hs : ∀ i, s ≠ z i) :
    -logDeriv (rationalMultiplier z m) s =
      polarSum (Finset.univ.image z) (multiplierWeight z m) s := by
  have hlog : logDeriv (rationalMultiplier z m) s = ∑ i, (m i : ℂ) / (s - z i) := by
    have hR : rationalMultiplier z m = fun x => ∏ i, (x - z i) ^ m i := rfl
    rw [hR, logDeriv_prod (f := fun i (x : ℂ) => (x - z i) ^ m i) (s := Finset.univ) (x := s)
      (fun i _ => zpow_ne_zero _ (sub_ne_zero.mpr (hs i)))
      (fun i _ => (differentiableAt_id.sub_const (z i)).zpow (Or.inl (sub_ne_zero.mpr (hs i))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_fun_zpow (f := fun x : ℂ => x - z i)
      (by fun_prop : DifferentiableAt ℂ (fun x : ℂ => x - z i) s), logDeriv_apply,
      deriv_sub_const, deriv_id'']
    simp [div_eq_mul_inv]
  rw [hlog, ← Finset.sum_fiberwise_of_maps_to (g := z) (t := Finset.univ.image z)
    (fun i _ => Finset.mem_image_of_mem z (Finset.mem_univ i)), ← Finset.sum_neg_distrib]
  unfold polarSum multiplierWeight netMultiplicity
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2], ← Finset.sum_div]
  push_cast
  ring

/-! ## §3. Classification: every rational deformation is anchored at a zero of `ξ` at height `γ` -/

/-- **Pole forcing.** If `Λ = Λ' · R` off the multiplier points with `Λ, Λ'` continuous and `R`
has a pole at `w` (`M(w) < 0`), then `Λ'(w) = 0`. -/
theorem eq_zero_of_pole_of_eq_mul_rationalMultiplier {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    {Λ Λ' : ℂ → ℂ} (hΛ : Continuous Λ) (hΛ' : Continuous Λ')
    (heq : ∀ s : ℂ, (∀ i, s ≠ z i) → Λ s = Λ' s * rationalMultiplier z m s)
    {w : ℂ} (hw : netMultiplicity z m w < 0) : Λ' w = 0 := by
  set k : ℕ := (-netMultiplicity z m w).toNat with hkdef
  have hk : (k : ℤ) = -netMultiplicity z m w := Int.toNat_of_nonneg (by omega)
  have hk1 : 1 ≤ k := by omega
  have hfin : ∀ᶠ s in 𝓝[≠] w, ∀ i, s ≠ z i := by
    refine Filter.eventually_all.mpr fun i => ?_
    by_cases hi : z i = w
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hi]; exact hs
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hi))
  have hev : ∀ᶠ s in 𝓝[≠] w, Λ s * (s - w) ^ k = Λ' s * multiplierCofactor z m w s := by
    filter_upwards [hfin, self_mem_nhdsWithin] with s hs hsw
    have hsw' : s - w ≠ 0 := sub_ne_zero.mpr hsw
    rw [heq s hs, rationalMultiplier_eq_zpow_mul_cofactor z m hsw,
      show ((s - w) ^ k : ℂ) = (s - w) ^ ((k : ℤ)) from (zpow_natCast _ _).symm, hk]
    calc Λ' s * ((s - w) ^ netMultiplicity z m w * multiplierCofactor z m w s) *
          (s - w) ^ (-netMultiplicity z m w)
        = Λ' s * multiplierCofactor z m w s *
            ((s - w) ^ netMultiplicity z m w * (s - w) ^ (-netMultiplicity z m w)) := by ring
      _ = Λ' s * multiplierCofactor z m w s := by
          rw [← zpow_add₀ hsw', add_neg_cancel, zpow_zero, mul_one]
  have hL : Tendsto (fun s => Λ s * (s - w) ^ k) (𝓝[≠] w) (𝓝 (Λ w * (w - w) ^ k)) :=
    ((hΛ.mul (by fun_prop : Continuous fun s : ℂ => (s - w) ^ k)).tendsto w).mono_left
      nhdsWithin_le_nhds
  have hR : Tendsto (fun s => Λ' s * multiplierCofactor z m w s) (𝓝[≠] w)
      (𝓝 (Λ' w * multiplierCofactor z m w w)) :=
    ((hΛ'.continuousAt.mul (multiplierCofactor_analyticAt z m w).continuousAt).tendsto).mono_left
      nhdsWithin_le_nhds
  have hlim := tendsto_nhds_unique (hL.congr' hev) hR
  rw [sub_self, zero_pow (by omega), mul_zero] at hlim
  exact (mul_eq_zero.mp hlim.symm).resolve_right (multiplierCofactor_self_ne_zero z m w)

/-- **Completion identity.** For a rational deformation, `Λ = Λ_γ · R` off the multiplier points
(identity theorem on the connected complement of a finite set). -/
theorem completion_eq_mul_rationalMultiplier {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s)
    {s : ℂ} (hs : ∀ i, s ≠ z i) :
    Λ s = heightCoupledΛ (fun s => 2 * RHTower.xi s) γ s * rationalMultiplier z m s := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ
  set V : Set ℂ := (Set.range z)ᶜ with hVdef
  have hVopen : IsOpen V := (Set.finite_range z).isClosed.isOpen_compl
  have hVconn : IsPreconnected V :=
    ((Set.finite_range z).countable.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have hmemV : ∀ x : ℂ, (∀ i, x ≠ z i) → x ∈ V := fun x hx ⟨i, hi⟩ => hx i hi.symm
  have hAΛ : AnalyticOnNhd ℂ Λ V := fun x _ => hHC.analyticOnNhd_univ x (Set.mem_univ x)
  have hAR : AnalyticOnNhd ℂ (fun x => Λγ x * rationalMultiplier z m x) V := fun x hx =>
    (hHC0.analyticOnNhd_univ x (Set.mem_univ x)).mul
      (rationalMultiplier_analyticAt z m fun i h => hx ⟨i, h.symm⟩)
  set a : ℝ := 2 + ∑ i, |(z i).re|
  have hza : ∀ i, (z i).re + 1 < a := fun i => by
    have h1 := Finset.single_le_sum (f := fun i => |(z i).re|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 := le_abs_self (z i).re
    linarith
  have hU : IsOpen {x : ℂ | a < x.re} := isOpen_lt continuous_const Complex.continuous_re
  set p : ℂ := ((a + 1 : ℝ) : ℂ)
  have hpU : p ∈ {x : ℂ | a < x.re} := by simp [p]
  have hpV : p ∈ V := hmemV p fun i h => by
    have := congrArg Complex.re h; simp [p] at this; linarith [hza i]
  have hev : Λ =ᶠ[𝓝 p] fun x => Λγ x * rationalMultiplier z m x := by
    filter_upwards [hU.mem_nhds hpU] with x hx
    have hx1 : 1 < x.re := by
      have : 0 ≤ ∑ i, |(z i).re| := Finset.sum_nonneg fun i _ => abs_nonneg _
      change a < x.re at hx; simp only [a] at hx; linarith
    rw [hHC.completed_eq x hx1, hF x hx1, hHC0.completed_eq x hx1]
    ring
  exact hAΛ.eqOn_of_preconnected_of_eventuallyEq hAR hVconn hpV hev (hmemV s hs)

/-- `ξ(σ + iγ) = 0` from a real zero `σ` of the height-coupled completion `Λ_γ`. -/
theorem xi_add_eq_zero_of_heightCoupledΛ_real_zero {γ σ : ℝ}
    (h : heightCoupledΛ (fun s => 2 * RHTower.xi s) γ (σ : ℂ) = 0) :
    RHTower.xi ((σ : ℂ) + (γ : ℂ) * I) = 0 := by
  have hZ := completedPositiveSystem_riemannZeta
  simp only [heightCoupledΛ] at h
  have hreal : (2 : ℂ) * RHTower.xi (σ : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (RHTower.xi_ne_zero_of_real σ)
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h'') hreal
    · exact (mul_eq_zero.mp h'').resolve_left two_ne_zero
  · have hc : (σ : ℂ) - (γ : ℂ) * I = conj ((σ : ℂ) + (γ : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hc] at h'
    have h'' : 2 * RHTower.xi (conj ((σ : ℂ) + (γ : ℂ) * I)) = 0 := h'
    rw [hZ.conj_Λ] at h''
    have := (map_eq_zero (starRingEnd ℂ)).mp h''
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- **Classification of rational deformations of `ζ_γ`.** Let `(F, Λ) ∈ HeightCoupledSystem 2 1 1 γ`
with `F = ζ_γ · ∏ᵢ (s − zᵢ)^{mᵢ}` on `Re s > 1`, and let `w₀` be a point of nonzero net
multiplicity with maximal real part. Then the multiplier has a **real pole** at `σ* = Re w₀`
(`M(σ*) < 0`) dominating every net multiplicity on the line `Re s = σ*`, and
`ξ(σ* + iγ) = 0`. -/
theorem rationalDeformation_real_anchor {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s)
    {w₀ : ℂ} (hw₀ : netMultiplicity z m w₀ ≠ 0)
    (htop : ∀ w : ℂ, netMultiplicity z m w ≠ 0 → w.re ≤ w₀.re) :
    netMultiplicity z m (w₀.re : ℂ) < 0 ∧
      (∀ β : ℝ, |netMultiplicity z m ((w₀.re : ℂ) + (β : ℂ) * I)| ≤
        -netMultiplicity z m (w₀.re : ℂ)) ∧
      RHTower.xi ((w₀.re : ℂ) + (γ : ℂ) * I) = 0 := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set S := Finset.univ.image z with hSdef
  set c := multiplierWeight z m with hcdef
  set a : ℝ := 2 + ∑ i, |(z i).re| with hadef
  have hsum_nn : 0 ≤ ∑ i, |(z i).re| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hza : ∀ i, (z i).re + 1 < a := fun i => by
    have h1 := Finset.single_le_sum (f := fun i => |(z i).re|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 := le_abs_self (z i).re
    linarith
  have ha1 : 1 < a := by linarith
  have hSa : ∀ w ∈ S, w.re ≤ a := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    linarith [hza i]
  have habs : LSeries.abscissaOfAbsConv (fun n => (heightCoupledVonMangoldt γ n : ℂ)) < a :=
    lt_of_le_of_lt (abscissaOfAbsConv_heightCoupledVonMangoldt_le_one γ) (by exact_mod_cast ha1)
  have hsplit : ∀ s : ℂ, a < s.re → -logDeriv F s =
      LSeries (fun n => (heightCoupledVonMangoldt γ n : ℂ)) s + polarSum S c s := by
    intro s hs
    have hs1 : 1 < s.re := by linarith
    have hsz : ∀ i, s ≠ z i := fun i h => by
      have := hza i; rw [← h] at this; linarith
    have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : F =ᶠ[𝓝 s] fun w => heightCoupledF riemannZeta γ w * rationalMultiplier z m w :=
      Filter.eventually_of_mem (hU.mem_nhds hs1) fun w hw => hF w hw
    have hlogF : logDeriv F s =
        logDeriv (fun w => heightCoupledF riemannZeta γ w * rationalMultiplier z m w) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    have hζγ_d : DifferentiableAt ℂ (heightCoupledF riemannZeta γ) s :=
      (hHC0.diffOn_F s hs1).differentiableAt (hU.mem_nhds hs1)
    have hR_ne : rationalMultiplier z m s ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (sub_ne_zero.mpr (hsz i))
    rw [hlogF, logDeriv_mul s (hHC0.ne_zero_F s hs1) hR_ne hζγ_d
      (rationalMultiplier_analyticAt z m hsz).differentiableAt, neg_add,
      neg_logDeriv_heightCoupledF_eq_LSeries γ hs1, neg_logDeriv_rationalMultiplier z m hsz]
  have hpd : ∀ σ : ℝ, a < σ → IsEvenPosDef fun u : ℝ =>
      (LSeries (fun n => (heightCoupledVonMangoldt γ n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
    intro σ hσ
    have h := hHC.posDef_neg_logDeriv (σ := σ) (by linarith)
    have heq : (fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (LSeries (fun n => (heightCoupledVonMangoldt γ n : ℂ))
          ((σ : ℂ) + (u : ℂ) * I) + polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u; rw [hsplit _ (by simpa using hσ)]
    rwa [heq] at h
  have hw₀S : w₀ ∈ S := by
    by_contra h
    exact hw₀ (netMultiplicity_eq_zero_of_notMem z m h)
  have hc₀ : c w₀ ≠ 0 := by simp [hcdef, multiplierWeight, hw₀]
  have htop' : ∀ w ∈ S, c w ≠ 0 → w.re ≤ w₀.re := fun w _ hw =>
    htop w (by simpa [hcdef, multiplierWeight] using hw)
  obtain ⟨_, hpos, hdom⟩ :=
    lattice_real_anchor (heightCoupledVonMangoldt_nonneg γ) hSa habs hpd hw₀S hc₀ htop'
  have hneg : netMultiplicity z m (w₀.re : ℂ) < 0 := by
    have : ((netMultiplicity z m (w₀.re : ℂ) : ℤ) : ℝ) < 0 := by
      simpa [hcdef, multiplierWeight] using hpos
    exact_mod_cast this
  refine ⟨hneg, fun β => ?_, ?_⟩
  · by_cases hβ : ((w₀.re : ℂ) + (β : ℂ) * I) ∈ S
    · have h := hdom β hβ
      simp only [hcdef, multiplierWeight, abs_neg] at h
      exact_mod_cast h
    · rw [netMultiplicity_eq_zero_of_notMem z m hβ, abs_zero]
      omega
  · apply xi_add_eq_zero_of_heightCoupledΛ_real_zero
    exact eq_zero_of_pole_of_eq_mul_rationalMultiplier hHC.entire_Λ.continuous
      hHC0.entire_Λ.continuous (fun s hs => completion_eq_mul_rationalMultiplier hHC hF hs) hneg

/-! ## §4. Rational rigidity off the zero ordinates -/

theorem rationalMultiplier_eq_one_of_netMultiplicity_eq_zero {n : ℕ} {z : Fin n → ℂ}
    {m : Fin n → ℤ} (h : ∀ w, netMultiplicity z m w = 0) {s : ℂ} (hs : ∀ i, s ≠ z i) :
    rationalMultiplier z m s = 1 := by
  unfold rationalMultiplier
  rw [← Finset.prod_fiberwise_of_maps_to (g := z) (t := Finset.univ.image z)
    (fun i _ => Finset.mem_image_of_mem z (Finset.mem_univ i))]
  refine Finset.prod_eq_one fun w hw => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
  rw [Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2],
    prod_zpow_eq_zpow_sum (sub_ne_zero.mpr (hs j))]
  have := h (z j)
  unfold netMultiplicity at this
  rw [this, zpow_zero]

/-- A nonzero net multiplicity has a rightmost representative. -/
theorem exists_top_netMultiplicity {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ} {w : ℂ}
    (hw : netMultiplicity z m w ≠ 0) :
    ∃ w₀, netMultiplicity z m w₀ ≠ 0 ∧ ∀ w', netMultiplicity z m w' ≠ 0 → w'.re ≤ w₀.re := by
  classical
  set T := (Finset.univ.image z).filter fun w => netMultiplicity z m w ≠ 0
  have hwT : w ∈ T := Finset.mem_filter.mpr
    ⟨by by_contra h; exact hw (netMultiplicity_eq_zero_of_notMem z m h), hw⟩
  obtain ⟨w₀, hw₀T, hmax⟩ := Finset.exists_max_image T (fun w => w.re) ⟨w, hwT⟩
  refine ⟨w₀, (Finset.mem_filter.mp hw₀T).2, fun w' hw' => hmax w' ?_⟩
  exact Finset.mem_filter.mpr
    ⟨by by_contra h; exact hw' (netMultiplicity_eq_zero_of_notMem z m h), hw'⟩

/-- A nontrivial rational deformation exists only at heights carrying a zero of `ξ`. -/
theorem netMultiplicity_eq_zero_of_xi_ne_zero_on_line {γ : ℝ}
    (hγ : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) ≠ 0) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s)
    (w : ℂ) : netMultiplicity z m w = 0 := by
  by_contra hw
  obtain ⟨w₀, hw₀, htop⟩ := exists_top_netMultiplicity hw
  exact hγ _ (rationalDeformation_real_anchor hHC hF hw₀ htop).2.2

/-- **Rational rigidity of `ζ_γ` off the zero ordinates.** If `ξ` has no zero on the horizontal line
`Im s = γ`, every rational deformation of `ζ_γ` inside `HeightCoupledSystem 2 1 1 γ` is trivial:
`F = ζ_γ` on `Re s > 1` and `Λ = Λ_γ`. -/
theorem rationalDeformation_rigid_of_xi_ne_zero_on_line {γ : ℝ}
    (hγ : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) ≠ 0) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s) :
    (∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s) ∧
      Λ = heightCoupledΛ (fun s => 2 * RHTower.xi s) γ := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have hM := netMultiplicity_eq_zero_of_xi_ne_zero_on_line hγ hHC hF
  have hR1 : ∀ s : ℂ, (∀ i, s ≠ z i) → rationalMultiplier z m s = 1 := fun s hs =>
    rationalMultiplier_eq_one_of_netMultiplicity_eq_zero hM hs
  have hoff : ∀ x : ℂ, ∀ᶠ s in 𝓝[≠] x, ∀ i, s ≠ z i := by
    intro x
    refine Filter.eventually_all.mpr fun i => ?_
    by_cases hi : z i = x
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hi]; exact hs
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hi))
  -- `Λ = Λ_γ` everywhere: agreement off the finite multiplier set, then continuity
  have hΛ : ∀ x : ℂ, Λ x = heightCoupledΛ (fun s => 2 * RHTower.xi s) γ x := by
    intro x
    have hev : ∀ᶠ s in 𝓝[≠] x, Λ s = heightCoupledΛ (fun s => 2 * RHTower.xi s) γ s := by
      filter_upwards [hoff x] with s hs
      rw [completion_eq_mul_rationalMultiplier hHC hF hs, hR1 s hs, mul_one]
    exact tendsto_nhds_unique
      ((hHC.entire_Λ.continuous.tendsto x).mono_left nhdsWithin_le_nhds)
      (((hHC0.entire_Λ.continuous.tendsto x).mono_left nhdsWithin_le_nhds).congr' (hev.mono
        fun s hs => hs.symm))
  refine ⟨fun x hx => ?_, funext hΛ⟩
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : ∀ᶠ s in 𝓝[≠] x, F s = heightCoupledF riemannZeta γ s := by
    filter_upwards [hoff x, nhdsWithin_le_nhds (hU.mem_nhds hx)] with s hs hs1
    rw [hF s hs1, hR1 s hs, mul_one]
  have hFc : ContinuousAt F x := (hHC.diffOn_F x hx).differentiableAt (hU.mem_nhds hx)
    |>.continuousAt
  have hζc : ContinuousAt (heightCoupledF riemannZeta γ) x :=
    (hHC0.diffOn_F x hx).differentiableAt (hU.mem_nhds hx) |>.continuousAt
  exact tendsto_nhds_unique (hFc.tendsto.mono_left nhdsWithin_le_nhds)
    ((hζc.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun s hs => hs.symm))

/-- **Unconditional rational rigidity of `ζ⁴`.** Since `ξ` has no real zero, the height-`0` carrier
`ζ(s)⁴` admits no nontrivial rational Bochner deformation. -/
theorem rationalDeformation_rigid_zero_height {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 0 F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta 0 s * rationalMultiplier z m s) :
    (∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta 0 s) ∧
      Λ = heightCoupledΛ (fun s => 2 * RHTower.xi s) 0 :=
  rationalDeformation_rigid_of_xi_ne_zero_on_line
    (fun x => by simpa using RHTower.xi_ne_zero_of_real x) hHC hF

/-! ## §5. The rational central ceiling and the Riemann Hypothesis -/

/-- `(F, Λ)` is a rational deformation of `ζ_γ` inside `HeightCoupledSystem 2 1 1 γ`. -/
def IsRationalCoupledDeformation (γ : ℝ) (F Λ : ℂ → ℂ) : Prop :=
  HeightCoupledSystem 2 1 1 γ F Λ ∧ ∃ (n : ℕ) (z : Fin n → ℂ) (m : Fin n → ℤ),
    ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s

/-- `CentralVanishingCeiling γ` restricted to rational deformations of `ζ_γ`. -/
def RationalCentralVanishingCeiling (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, IsRationalCoupledDeformation γ F Λ →
    (analyticOrderAt Λ (1 / 2)).toNat ≤
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat

theorem analyticOrderAt_sub_pow (w : ℂ) (k : ℕ) :
    analyticOrderAt (fun s : ℂ => (s - w) ^ k) w = k := by
  rw [((analyticAt_id.sub analyticAt_const).pow k).analyticOrderAt_eq_natCast]
  exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun s => by simp⟩

/-- **Exact central descent.** If `ξ` has no off-critical zero at ordinate `γ`, every rational
deformation of `ζ_γ` is either trivial (`Λ = Λ_γ`) or carries a central pole of the multiplier
(`M(1/2) < 0`) and lowers the central vanishing order by exactly `−M(1/2) ≥ 1`. -/
theorem rationalDeformation_central_descent {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s) :
    Λ = heightCoupledΛ (fun s => 2 * RHTower.xi s) γ ∨
      (netMultiplicity z m (1 / 2) < 0 ∧
        (analyticOrderAt Λ (1 / 2)).toNat +
            (-netMultiplicity z m (1 / 2)).toNat =
          (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat) := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ with hΛγ
  by_cases htriv : ∀ w, netMultiplicity z m w = 0
  · left
    have hγline : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) ≠ 0 ∨ True := fun _ => Or.inr trivial
    clear hγline
    -- trivial multiplier: reuse the rigidity argument through `R = 1`
    have hR1 : ∀ s : ℂ, (∀ i, s ≠ z i) → rationalMultiplier z m s = 1 := fun s hs =>
      rationalMultiplier_eq_one_of_netMultiplicity_eq_zero htriv hs
    funext x
    have hoffx : ∀ᶠ s in 𝓝[≠] x, ∀ i, s ≠ z i := by
      refine Filter.eventually_all.mpr fun i => ?_
      by_cases hi : z i = x
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hi]; exact hs
      · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hi))
    have hev : ∀ᶠ s in 𝓝[≠] x, Λ s = Λγ s := by
      filter_upwards [hoffx] with s hs
      rw [completion_eq_mul_rationalMultiplier hHC hF hs, hR1 s hs, mul_one]
    exact tendsto_nhds_unique
      ((hHC.entire_Λ.continuous.tendsto x).mono_left nhdsWithin_le_nhds)
      (((hHC0.entire_Λ.continuous.tendsto x).mono_left nhdsWithin_le_nhds).congr' (hev.mono
        fun s hs => hs.symm))
  right
  obtain ⟨w, hw⟩ := not_forall.mp htriv
  obtain ⟨w₀, hw₀, htop⟩ := exists_top_netMultiplicity hw
  obtain ⟨hneg, -, hxi⟩ := rationalDeformation_real_anchor hHC hF hw₀ htop
  have hσ : w₀.re = 1 / 2 := hoff _ hxi
  have hhalf : ((w₀.re : ℝ) : ℂ) = 1 / 2 := by rw [hσ]; push_cast; ring
  rw [hhalf] at hneg
  refine ⟨hneg, ?_⟩
  set k : ℕ := (-netMultiplicity z m (1 / 2)).toNat with hkdef
  have hk : (k : ℤ) = -netMultiplicity z m (1 / 2) := Int.toNat_of_nonneg (by omega)
  -- `Λ(s)(s − 1/2)^k = Λ_γ(s) R_{1/2}(s)` on a full neighbourhood of `1/2`
  have hoffh : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), ∀ i, s ≠ z i := by
    refine Filter.eventually_all.mpr fun i => ?_
    by_cases hi : z i = 1 / 2
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hi]; exact hs
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hi))
  have hpunct : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ),
      Λ s * (s - 1 / 2) ^ k = Λγ s * multiplierCofactor z m (1 / 2) s := by
    filter_upwards [hoffh, self_mem_nhdsWithin] with s hs hsw
    have hsw' : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr hsw
    rw [completion_eq_mul_rationalMultiplier hHC hF hs,
      rationalMultiplier_eq_zpow_mul_cofactor z m hsw,
      show ((s - 1 / 2) ^ k : ℂ) = (s - 1 / 2) ^ ((k : ℤ)) from (zpow_natCast _ _).symm, hk]
    calc Λγ s * ((s - 1 / 2) ^ netMultiplicity z m (1 / 2) * multiplierCofactor z m (1 / 2) s) *
          (s - 1 / 2) ^ (-netMultiplicity z m (1 / 2))
        = Λγ s * multiplierCofactor z m (1 / 2) s *
            ((s - 1 / 2) ^ netMultiplicity z m (1 / 2) *
              (s - 1 / 2) ^ (-netMultiplicity z m (1 / 2))) := by ring
      _ = Λγ s * multiplierCofactor z m (1 / 2) s := by
          rw [← zpow_add₀ hsw', add_neg_cancel, zpow_zero, mul_one]
  have hcL : Continuous fun s : ℂ => Λ s * (s - 1 / 2) ^ k :=
    hHC.entire_Λ.continuous.mul (by fun_prop)
  have hcR : ContinuousAt (fun s : ℂ => Λγ s * multiplierCofactor z m (1 / 2) s) (1 / 2) :=
    hHC0.entire_Λ.continuous.continuousAt.mul
      (multiplierCofactor_analyticAt z m (1 / 2)).continuousAt
  have hat : Λ (1 / 2) * (1 / 2 - 1 / 2) ^ k =
      Λγ (1 / 2) * multiplierCofactor z m (1 / 2) (1 / 2) :=
    tendsto_nhds_unique ((hcL.tendsto _).mono_left nhdsWithin_le_nhds)
      ((hcR.tendsto.mono_left nhdsWithin_le_nhds).congr' (hpunct.mono fun s hs => hs.symm))
  have hfull : (fun s : ℂ => Λ s * (s - 1 / 2) ^ k) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun s => Λγ s * multiplierCofactor z m (1 / 2) s := by
    have h := eventually_nhdsWithin_iff.mp hpunct
    filter_upwards [h] with s hs
    by_cases hsw : s = 1 / 2
    · rw [hsw]; exact hat
    · exact hs hsw
  have hordL : analyticOrderAt (fun s : ℂ => Λ s * (s - 1 / 2) ^ k) (1 / 2) =
      analyticOrderAt Λ (1 / 2) + k := by
    have hg : AnalyticAt ℂ (fun s : ℂ => (s - 1 / 2) ^ k) (1 / 2) :=
      (analyticAt_id.sub analyticAt_const).pow k
    rw [show (fun s : ℂ => Λ s * (s - 1 / 2) ^ k) = Λ * fun s : ℂ => (s - 1 / 2) ^ k from rfl,
      analyticOrderAt_mul (hHC.analyticOnNhd_univ _ (Set.mem_univ _)) hg,
      analyticOrderAt_sub_pow]
  have hordR : analyticOrderAt (fun s : ℂ => Λγ s * multiplierCofactor z m (1 / 2) s) (1 / 2) =
      analyticOrderAt Λγ (1 / 2) := by
    rw [show (fun s : ℂ => Λγ s * multiplierCofactor z m (1 / 2) s) =
        Λγ * multiplierCofactor z m (1 / 2) from rfl,
      analyticOrderAt_mul (hHC0.analyticOnNhd_univ _ (Set.mem_univ _))
        (multiplierCofactor_analyticAt z m (1 / 2)),
      (multiplierCofactor_analyticAt z m (1 / 2)).analyticOrderAt_eq_zero.mpr
        (multiplierCofactor_self_ne_zero z m (1 / 2)), add_zero]
  have hord := analyticOrderAt_congr hfull
  rw [hordL, hordR] at hord
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (hHC0.orderAt_ne_top (1 / 2))
  rw [← hb] at hord ⊢
  obtain ⟨a', ha'⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top (1 / 2))
  rw [← ha'] at hord ⊢
  rw [ENat.toNat_coe, ENat.toNat_coe]
  exact_mod_cast hord

/-- **Rational central ceiling from a zero-free horizontal line off the critical point.** -/
theorem rationalCentralVanishingCeiling_of_offCritical_free {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) :
    RationalCentralVanishingCeiling γ := by
  rintro F Λ ⟨hHC, n, z, m, hF⟩
  rcases rationalDeformation_central_descent hoff hHC hF with h | ⟨-, h⟩
  · rw [h]
  · omega

/-! ## §6. The converse: off-critical quartets, and the Riemann Hypothesis -/

/-- Multiplier points of the coupled quartet contraction `coupledQuartetSymSquare a a γ`. -/
def quartetMultiplierPoints (a γ : ℝ) : Fin 9 → ℂ :=
  ![1 / 2, 1 / 2 + (γ : ℂ) * I, 1 / 2 - (γ : ℂ) * I, 1 / 2 + (a : ℂ), 1 / 2 - (a : ℂ),
    1 / 2 + (a : ℂ) + (γ : ℂ) * I, 1 / 2 + (a : ℂ) - (γ : ℂ) * I,
    1 / 2 - (a : ℂ) + (γ : ℂ) * I, 1 / 2 - (a : ℂ) - (γ : ℂ) * I]

/-- Exponents of the coupled quartet contraction: a central zero of order `4`, double zeros at
`1/2 ± iγ`, double poles at `1/2 ± a`, simple poles at the quartet `1/2 ± a ± iγ`. -/
def quartetMultiplierOrders : Fin 9 → ℤ := ![4, 2, 2, -2, -2, -1, -1, -1, -1]

/-- The off-critical quartet contraction is a rational multiplier. -/
theorem coupledQuartetSymSquare_eq_rationalMultiplier {a γ : ℝ} (ha : |a| < 1 / 2) {s : ℂ}
    (hs : 1 < s.re) :
    coupledQuartetSymSquare a a γ s =
      rationalMultiplier (quartetMultiplierPoints a γ) quartetMultiplierOrders s := by
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  have hre : ∀ x : ℂ, x.re < 1 → s - x ≠ 0 := fun x hx h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hq : ∀ x : ℂ, (s - x) ^ 2 + (γ : ℂ) ^ 2 =
      (s - (x + (γ : ℂ) * I)) * (s - (x - (γ : ℂ) * I)) := fun x => by
    ring_nf; rw [Complex.I_sq]; ring
  have e1 := hre (1 / 2 + (a : ℂ)) (by simp; linarith)
  have e2 := hre (1 / 2 - (a : ℂ)) (by simp; linarith)
  have e3 := hre (1 / 2 + (a : ℂ) + (γ : ℂ) * I) (by simp; linarith)
  have e4 := hre (1 / 2 + (a : ℂ) - (γ : ℂ) * I) (by simp; linarith)
  have e5 := hre (1 / 2 - (a : ℂ) + (γ : ℂ) * I) (by simp; linarith)
  have e6 := hre (1 / 2 - (a : ℂ) - (γ : ℂ) * I) (by simp; linarith)
  unfold coupledQuartetSymSquare midpointSymSquare quartetCritPoly quartetOffPoly realPairPoly
    rationalMultiplier
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, quartetMultiplierPoints,
    quartetMultiplierOrders, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  rw [show ((1 / 2 + a : ℝ) : ℂ) = 1 / 2 + (a : ℂ) by push_cast; ring,
    show ((1 - (1 / 2 + a) : ℝ) : ℂ) = 1 / 2 - (a : ℂ) by push_cast; ring,
    show ((1 / 2 - a : ℝ) : ℂ) = 1 / 2 - (a : ℂ) by push_cast; ring,
    hq (1 / 2 + (a : ℂ)), hq (1 / 2 - (a : ℂ)), hq (1 / 2)]
  simp only [zpow_neg, zpow_ofNat]
  field_simp

/-- **Off-critical zeros produce rational deformations above the central ceiling.** If
`ξ(1/2 + a + iγ) = 0` with `0 < a < 1/2`, `γ ≠ 0`, the coupled quartet contraction is a rational
deformation of `ζ_γ` raising the central vanishing order by exactly `4`. -/
theorem exists_rationalDeformation_above_ceiling {γ a : ℝ} (hγ : γ ≠ 0) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (hxi : RHTower.xi (1 / 2 + a + γ * I) = 0) :
    ∃ F Λ : ℂ → ℂ, IsRationalCoupledDeformation γ F Λ ∧
      (analyticOrderAt Λ (1 / 2)).toNat =
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat + 4 := by
  have hZ := completedPositiveSystem_riemannZeta
  have hq : (fun s => 2 * RHTower.xi s) (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 := by
    simp only [hxi, mul_zero]
  obtain ⟨Λc, hHCc, hord⟩ :=
    CompletedPositiveSystem.contractComplexQuartet_heightCoupled hZ ha0 ha1 hγ hq
  refine ⟨_, Λc, ⟨hHCc, 9, quartetMultiplierPoints a γ, quartetMultiplierOrders,
    fun s hs => by
      rw [coupledQuartetSymSquare_eq_rationalMultiplier (abs_lt.mpr ⟨by linarith, ha1⟩) hs]⟩, ?_⟩
  have h0 := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hZ γ (1 / 2)
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at h0
  omega

/-- **The rational central ceiling is exactly a horizontal zero-free line.** For `γ ≠ 0`,
`RationalCentralVanishingCeiling γ` holds iff `ξ` has no off-critical zero at ordinate `γ`. -/
theorem rationalCentralVanishingCeiling_iff {γ : ℝ} (hγ : γ ≠ 0) :
    RationalCentralVanishingCeiling γ ↔
      ∀ a : ℝ, 0 < a → a < 1 / 2 → RHTower.xi (1 / 2 + a + γ * I) ≠ 0 := by
  constructor
  · intro hceil a ha0 ha1 hxi
    obtain ⟨F, Λ, hdef, hord⟩ := exists_rationalDeformation_above_ceiling hγ ha0 ha1 hxi
    have := hceil F Λ hdef
    omega
  · intro hfree
    refine rationalCentralVanishingCeiling_of_offCritical_free fun x hx => ?_
    have hZ := completedPositiveSystem_riemannZeta
    have hpos := RHTower.xi_zero_re_pos hx
    have hlt := RHTower.xi_zero_re_lt_one hx
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at hpos hlt
    rcases lt_trichotomy x (1 / 2) with hx' | hx' | hx'
    · exfalso
      refine hfree (1 / 2 - x) (by linarith) (by linarith) ?_
      have h1 : RHTower.xi (1 - ((x : ℂ) + (γ : ℂ) * I)) = 0 := by
        rw [RHTower.xi_one_sub]; exact hx
      have hc : (1 / 2 : ℂ) + ((1 / 2 - x : ℝ) : ℂ) + (γ : ℂ) * I =
          conj (1 - ((x : ℂ) + (γ : ℂ) * I)) :=
        Complex.ext (by simp; ring) (by simp)
      rw [hc]
      have h2 : 2 * RHTower.xi (conj (1 - ((x : ℂ) + (γ : ℂ) * I))) = 0 := by
        rw [hZ.conj_Λ]; simp [h1]
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    · exact hx'
    · exfalso
      refine hfree (x - 1 / 2) (by linarith) (by linarith) ?_
      rw [show (1 / 2 : ℂ) + ((x - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I = (x : ℂ) + (γ : ℂ) * I by
        push_cast; ring]
      exact hx

/-- **The Riemann Hypothesis is the rational chiral ceiling at every height.**
RH holds iff, at every ordinate `γ ≠ 0`, no rational Bochner deformation of the height-coupled
carrier `ζ_γ` exceeds its central vanishing order. -/
theorem riemannHypothesis_iff_forall_rationalCentralVanishingCeiling :
    RiemannHypothesis ↔ ∀ γ : ℝ, γ ≠ 0 → RationalCentralVanishingCeiling γ := by
  constructor
  · intro hRH γ hγ
    refine (rationalCentralVanishingCeiling_iff hγ).mpr fun a ha0 ha1 hxi => ?_
    set s : ℂ := 1 / 2 + a + γ * I
    have hsre : s.re = 1 / 2 + a := by simp [s]
    have hs1 : s ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
    have hz : riemannZeta s = 0 :=
      (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by rw [hsre]; linarith) hs1).mp hxi
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      rw [hsre] at this
      simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have := hRH s hz htriv hs1
    rw [hsre] at this
    linarith
  · intro h
    rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro s hs1 hs2 hz
    have him : s.im ≠ 0 := zeta_strip_zero_im_ne_zero hz (by linarith) hs2
    have hs : s = 1 / 2 + ((s.re - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp
    have hne1 : s ≠ 1 := by
      intro h1; rw [h1] at hs2; simp at hs2
    have hxi : RHTower.xi s = 0 :=
      (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mpr hz
    rw [hs] at hxi
    exact (rationalCentralVanishingCeiling_iff him).mp (h _ him) (s.re - 1 / 2) (by linarith)
      (by linarith) hxi

end GaloisForLFunctions.BiarithmeticGaugeGeometry
