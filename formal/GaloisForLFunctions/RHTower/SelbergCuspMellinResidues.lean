import GaloisForLFunctions.RHTower.SelbergThetaMellinBarnes
import GaloisForLFunctions.HTGeometry.FinitePoleVerticalContourShift
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Poles and residues of the cusp Mellin–Barnes integrand

For a class member `F` of degree `d`, a base point `s` and a nonzero base `x`, the integrand

```text
g(u) = x^{-u} Γ(u) F(s + u/d)
```

is meromorphic everywhere, analytic off the Gamma poles `u = -k` and the point `u₀ = d(1 - s)`
where `F` has its pole (`ExtendedSelbergClass.analyticAt_cuspMellinIntegrand`).  At `u = -k`
(`k ∈ ℕ`, `u₀ ≠ -k`) the pole is simple with residue `x^k (-1)^k/k! · F(s - k/d)`
(`ExtendedSelbergClass.laurentCoeff_cuspMellinIntegrand_neg_nat`).

The residue at `u₀` is the singular part of the cusp expansion.  With `x = -2πiζ` it is an
analytic function of `ζ` on the upper half plane (`ExtendedSelbergClass.analyticOnNhd_cuspPolarPart`):
it is `(-2πiζ)^{-u₀}` times a polynomial in `log(-2πiζ)`, by the Leibniz rule applied to the
clearing shift.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The cusp Mellin–Barnes integrand `x^{-u} Γ(u) F(s + u/d)`. -/
def ExtendedSelbergClass.cuspMellinIntegrand (F : ExtendedSelbergClass) (s x : ℂ) (u : ℂ) : ℂ :=
  x ^ (-u) * (Complex.Gamma u * F (s + u / (F.gammaData.degree : ℂ)))

/-- The point `u₀ = d(1 - s)` at which the pole of `F` enters the integrand. -/
def ExtendedSelbergClass.cuspPole (F : ExtendedSelbergClass) (s : ℂ) : ℂ :=
  (F.gammaData.degree : ℂ) * (1 - s)

theorem ExtendedSelbergClass.add_div_eq_one_iff (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s u : ℂ) :
    s + u / (F.gammaData.degree : ℂ) = 1 ↔ u = F.cuspPole s := by
  have hdne : (F.gammaData.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  rw [ExtendedSelbergClass.cuspPole]
  constructor
  · intro h
    have h' : u / (F.gammaData.degree : ℂ) = 1 - s := by rw [← h]; ring
    rw [div_eq_iff hdne] at h'
    rw [h']
    ring
  · intro h
    rw [h]
    field_simp
    ring

theorem ExtendedSelbergClass.analyticAt_comp_affine (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s : ℂ) {u : ℂ} (hu : u ≠ F.cuspPole s) :
    AnalyticAt ℂ (fun u => F (s + u / (F.gammaData.degree : ℂ))) u := by
  have hne : s + u / (F.gammaData.degree : ℂ) ≠ 1 := fun h =>
    hu ((F.add_div_eq_one_iff hd s u).1 h)
  have hF := F.continuation.analyticAt_value_of_ne_one hne
  exact AnalyticAt.comp (g := F.continuation.value)
    (f := fun u => s + u / (F.gammaData.degree : ℂ)) (x := u) hF (by fun_prop)

theorem analyticAt_cpow_neg {x : ℂ} (hx : x ≠ 0) (u : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => x ^ (-u)) u :=
  (Differentiable.const_cpow differentiable_neg (Or.inl hx)).analyticAt u

theorem ExtendedSelbergClass.analyticAt_cuspMellinIntegrand (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s : ℂ) {x : ℂ} (hx : x ≠ 0) {u : ℂ}
    (hΓ : ∀ k : ℕ, u ≠ -(k : ℂ)) (hu : u ≠ F.cuspPole s) :
    AnalyticAt ℂ (F.cuspMellinIntegrand s x) u :=
  (analyticAt_cpow_neg hx u).mul
    ((HTGeometry.analyticAt_Gamma_off_poles hΓ).mul (F.analyticAt_comp_affine hd s hu))

theorem ExtendedSelbergClass.meromorphicAt_cuspMellinIntegrand (F : ExtendedSelbergClass)
    (s : ℂ) {x : ℂ} (hx : x ≠ 0) (u : ℂ) :
    MeromorphicAt (F.cuspMellinIntegrand s x) u := by
  have hF : MeromorphicAt (fun u => F (s + u / (F.gammaData.degree : ℂ))) u :=
    (F.meromorphic_value _).comp_analyticAt (by fun_prop)
  exact (analyticAt_cpow_neg hx u).meromorphicAt.mul ((Meromorphic.Gamma u).mul hF)

/-- `Γ(u + n) = (∏_{j<n} (u + j)) Γ(u)` away from the poles crossed. -/
theorem Gamma_add_nat_eq_prod_mul (u : ℂ) (n : ℕ) (hu : ∀ j < n, u + j ≠ 0) :
    Complex.Gamma (u + n) = (∏ j ∈ Finset.range n, (u + j)) * Complex.Gamma u := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hun : u + n ≠ 0 := hu n (Nat.lt_succ_self n)
      rw [show u + ((n + 1 : ℕ) : ℂ) = (u + n) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hun, ih fun j hj => hu j (Nat.lt_succ_of_lt hj),
        Finset.prod_range_succ]
      ring

theorem prod_range_neg_nat_add (k : ℕ) :
    ∏ j ∈ Finset.range k, (-(k : ℂ) + j) = (-1) ^ k * (k.factorial : ℂ) := by
  have h : ∏ j ∈ Finset.range k, (-(k : ℂ) + j) = ∏ j ∈ Finset.range k, (-1 * ((k - j : ℕ) : ℂ)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≤ k := (Finset.mem_range.1 hj).le
    rw [Nat.cast_sub hjk]
    ring
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  congr 1
  calc ∏ x ∈ Finset.range k, ((k - x : ℕ) : ℂ)
      = ∏ x ∈ Finset.range k, (((k - 1 - x) + 1 : ℕ) : ℂ) := by
        refine Finset.prod_congr rfl fun x hx => ?_
        have hx' := Finset.mem_range.1 hx
        congr 1
        omega
    _ = ∏ x ∈ Finset.range k, ((x + 1 : ℕ) : ℂ) :=
        Finset.prod_range_reflect (fun x => ((x + 1 : ℕ) : ℂ)) k
    _ = (k.factorial : ℂ) := by
        rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

/-- **The residue at a Gamma pole.** -/
theorem ExtendedSelbergClass.laurentCoeff_cuspMellinIntegrand_neg_nat (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s : ℂ) {x : ℂ} (hx : x ≠ 0) (k : ℕ)
    (hk : F.cuspPole s ≠ -(k : ℂ)) :
    laurentCoeff (F.cuspMellinIntegrand s x) (-(k : ℂ)) (-1) =
      x ^ k * ((-1) ^ k / (k.factorial : ℂ)) * F (s - k / (F.gammaData.degree : ℂ)) := by
  set G : ℂ → ℂ := fun u => x ^ (-u) * F (s + u / (F.gammaData.degree : ℂ)) *
    (Complex.Gamma (u + (k + 1 : ℕ)) * (∏ j ∈ Finset.range k, (u + j))⁻¹) with hGdef
  have hprod_ne : ∏ j ∈ Finset.range k, (-(k : ℂ) + j) ≠ 0 := by
    rw [prod_range_neg_nat_add]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast k.factorial_ne_zero)
  have hG : AnalyticAt ℂ G (-(k : ℂ)) := by
    have h1 : AnalyticAt ℂ (fun u => F (s + u / (F.gammaData.degree : ℂ))) (-(k : ℂ)) :=
      F.analyticAt_comp_affine hd s (Ne.symm hk)
    have h2 : AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (u + (k + 1 : ℕ))) (-(k : ℂ)) := by
      have hre : 0 < (-(k : ℂ) + ((k + 1 : ℕ) : ℂ)).re := by push_cast; simp
      exact AnalyticAt.comp (g := Complex.Gamma) (f := fun u : ℂ => u + ((k + 1 : ℕ) : ℂ))
        (x := -(k : ℂ)) (HTGeometry.analyticAt_Gamma_of_re_pos hre) (by fun_prop)
    have h3 : AnalyticAt ℂ (fun u : ℂ => (∏ j ∈ Finset.range k, (u + j))⁻¹) (-(k : ℂ)) := by
      refine AnalyticAt.inv ?_ hprod_ne
      exact Finset.analyticAt_fun_prod _ fun j _ => by fun_prop
    exact ((analyticAt_cpow_neg hx _).mul h1).mul (h2.mul h3)
  have hf : ∀ᶠ u in 𝓝[≠] (-(k : ℂ)), F.cuspMellinIntegrand s x u = G u / (u - (-(k : ℂ))) := by
    have hball : ∀ᶠ u in 𝓝 (-(k : ℂ)), dist u (-(k : ℂ)) < 1 / 2 :=
      Metric.eventually_nhds_iff.2 ⟨1 / 2, by norm_num, fun _ h => h⟩
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with u hu hune
    have hune' : u ≠ -(k : ℂ) := hune
    have hnz : ∀ j < k + 1, u + j ≠ 0 := by
      intro j hj h0
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | rfl
      · have : dist u (-(k : ℂ)) = ((k - j : ℕ) : ℝ) := by
          rw [Complex.dist_eq, show u - -(k : ℂ) = (u + j) + ((k - j : ℕ) : ℂ) by
            push_cast [Nat.cast_sub hjk.le]; ring, h0, zero_add, Complex.norm_natCast]
        rw [this] at hu
        have : (1 : ℝ) ≤ ((k - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k - j)
        linarith
      · exact hune' (by linear_combination h0)
    have hΓ := Gamma_add_nat_eq_prod_mul u (k + 1) hnz
    rw [Finset.prod_range_succ] at hΓ
    have hpk : ∏ j ∈ Finset.range k, (u + j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => hnz j (by have := Finset.mem_range.1 hj; omega)
    have huk : u - -(k : ℂ) ≠ 0 := sub_ne_zero.2 hune'
    have huk' : u + (k : ℂ) = u - -(k : ℂ) := by ring
    simp only [hGdef, ExtendedSelbergClass.cuspMellinIntegrand]
    rw [hΓ, eq_div_iff huk, show u - -(k : ℂ) = u + k by ring]
    field_simp
  rw [laurentCoeff_neg_one_of_eq_div hG hf]
  simp only [hGdef]
  rw [show -(k : ℂ) + ((k + 1 : ℕ) : ℂ) = 1 by push_cast; ring, Complex.Gamma_one, one_mul,
    prod_range_neg_nat_add, neg_neg, Complex.cpow_natCast,
    show s + -(k : ℂ) / (F.gammaData.degree : ℂ) = s - k / (F.gammaData.degree : ℂ) by ring]
  have hsign : ((-1 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ = (-1) ^ k / (k.factorial : ℂ) := by
    rw [mul_inv, ← inv_pow, inv_neg, inv_one, div_eq_mul_inv]
  rw [hsign]
  ring

/-! ## The singular part at the pole of `F` -/

/-- The singular part of the cusp expansion: the residue of the integrand at `u₀` with base
`x = -2πiζ`. -/
def ExtendedSelbergClass.cuspPolarPart (F : ExtendedSelbergClass) (s ζ : ℂ) : ℂ :=
  laurentCoeff (F.cuspMellinIntegrand s (-2 * Real.pi * Complex.I * ζ)) (F.cuspPole s) (-1)

/-- The base `-2πiζ` lies in the right half plane when `ζ` lies in the upper half plane. -/
theorem neg_two_pi_I_mul_mem_slitPlane {ζ : ℂ} (hζ : 0 < ζ.im) :
    -2 * Real.pi * Complex.I * ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have : (-2 * Real.pi * Complex.I * ζ).re = 2 * Real.pi * ζ.im := by simp
  rw [this]
  positivity

theorem neg_two_pi_I_mul_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) : -2 * Real.pi * Complex.I * ζ ≠ 0 :=
  Complex.slitPlane_ne_zero (neg_two_pi_I_mul_mem_slitPlane hζ)

/-- **The singular part is analytic in `ζ` on the upper half plane.** -/
theorem ExtendedSelbergClass.analyticOnNhd_cuspPolarPart (F : ExtendedSelbergClass) (s : ℂ) :
    AnalyticOnNhd ℂ (F.cuspPolarPart s) {ζ : ℂ | 0 < ζ.im} := by
  set u₀ := F.cuspPole s
  set A : ℂ → ℂ := fun u => Complex.Gamma u * F (s + u / (F.gammaData.degree : ℂ)) with hA
  have hAmero : MeromorphicAt A u₀ :=
    (Meromorphic.Gamma u₀).mul ((F.meromorphic_value _).comp_analyticAt (by fun_prop))
  obtain ⟨k, hk1, hkB⟩ := exists_analyticAt_laurentShift_ge hAmero 1
  set B := laurentShift A u₀ k with hBdef
  set L : ℂ → ℂ := fun ζ => Complex.log (-2 * Real.pi * Complex.I * ζ) with hL
  set β : ℕ → ℂ := fun j => iteratedDeriv j B 0 with hβ
  set Q : ℂ → ℂ := fun ζ => ((k - 1).factorial : ℂ)⁻¹ *
    ∑ i ∈ Finset.range k, ((k - 1).choose i : ℂ) *
      (Complex.exp (-u₀ * L ζ) * (-L ζ) ^ i) * β (k - 1 - i) with hQ
  -- the explicit formula on the upper half plane
  have hformula : ∀ ζ : ℂ, 0 < ζ.im → F.cuspPolarPart s ζ = Q ζ := by
    intro ζ hζ
    set x : ℂ := -2 * Real.pi * Complex.I * ζ with hx
    have hx0 : x ≠ 0 := neg_two_pi_I_mul_ne_zero hζ
    set E : ℂ → ℂ := fun t => Complex.exp (-u₀ * L ζ) * Complex.exp (-L ζ * t) with hE
    have hshift : laurentShift (F.cuspMellinIntegrand s x) u₀ k = fun t => E t * B t := by
      funext t
      simp only [laurentShift, hE, hBdef, ExtendedSelbergClass.cuspMellinIntegrand, hA]
      rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.exp_add]
      have : Complex.log x * -(u₀ + t) = -u₀ * L ζ + -L ζ * t := by
        simp only [hL, hx]; ring
      rw [this]
      ring
    have hEan : AnalyticAt ℂ E 0 := by fun_prop
    have hana : AnalyticAt ℂ (laurentShift (F.cuspMellinIntegrand s x) u₀ k) 0 := by
      rw [hshift]; exact hEan.mul hkB
    have hℓ : (0 : ℤ) ≤ -1 + (k : ℤ) := by omega
    rw [ExtendedSelbergClass.cuspPolarPart, laurentCoeff_eq_taylorCoeffZero hana hℓ, hshift]
    have hidx : ((-1 : ℤ) + (k : ℤ)).toNat = k - 1 := by omega
    rw [hidx, taylorCoeffZero]
    have hmul : (fun t => E t * B t) = E * B := rfl
    rw [hmul, iteratedDeriv_mul hEan.contDiffAt hkB.contDiffAt]
    have hEder : ∀ i : ℕ, iteratedDeriv i E 0 = Complex.exp (-u₀ * L ζ) * (-L ζ) ^ i := by
      intro i
      have h1 : iteratedDeriv i E 0 =
          Complex.exp (-u₀ * L ζ) * iteratedDeriv i (fun t => Complex.exp (-L ζ * t)) 0 :=
        iteratedDeriv_const_mul_field _ _
      rw [h1, iteratedDeriv_cexp_const_mul]
      simp
    simp_rw [hEder]
    rw [hQ, div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr (by rw [Nat.sub_add_cancel (by omega)]) fun i _ => ?_
    simp only [hβ]
  -- analyticity of the explicit formula
  intro ζ₀ hζ₀
  have hζ₀' : 0 < ζ₀.im := hζ₀
  have hLan : AnalyticAt ℂ L ζ₀ :=
    (analyticAt_clog (neg_two_pi_I_mul_mem_slitPlane hζ₀')).comp (by fun_prop)
  have hQan : AnalyticAt ℂ Q ζ₀ := by
    simp only [hQ]
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => ?_)
    exact (analyticAt_const.mul (((analyticAt_const.mul hLan).cexp).mul
      (hLan.neg.pow i))).mul analyticAt_const
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  refine hQan.congr ?_
  filter_upwards [hopen.mem_nhds hζ₀] with ζ hζ
  exact (hformula ζ hζ).symm

end

end RHTower
