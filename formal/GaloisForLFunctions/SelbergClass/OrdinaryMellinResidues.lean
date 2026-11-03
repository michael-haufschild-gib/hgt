import GaloisForLFunctions.SelbergClass.OrdinaryMellinLeftDecay

/-!
# Residues of the ordinary exponential Mellin transform

At the nonpositive integers the residues are the ordinary Taylor coefficients.
The possible pole at one contributes a function analytic on the slit plane.
-/

noncomputable section
open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

/-- The possible polar contribution at one, with arbitrary pole order. -/
def ordinaryPolarPart (F : ExtendedSelbergClass) (z : ℂ) : ℂ :=
  laurentCoeff (ordinaryMellinIntegrand F 0 z) 1 (-1)

/-- Residue at a Gamma pole. The pole of the class member lies at one and never
collides with these points. -/
theorem laurentCoeff_ordinaryMellinIntegrand_neg_nat (F : ExtendedSelbergClass)
    {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    laurentCoeff (ordinaryMellinIntegrand F 0 z) (-(k : ℂ)) (-1) =
      z ^ k * ((-1) ^ k / (k.factorial : ℂ)) * F (-(k : ℂ)) := by
  set G : ℂ → ℂ := fun u => z ^ (-u) * F u *
    (Complex.Gamma (u + (k + 1 : ℕ)) * (∏ j ∈ Finset.range k, (u + j))⁻¹) with hGdef
  have hprod_ne : ∏ j ∈ Finset.range k, (-(k : ℂ) + j) ≠ 0 := by
    rw [prod_range_neg_nat_add]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast k.factorial_ne_zero)
  have hG : AnalyticAt ℂ G (-(k : ℂ)) := by
    have hk1 : -(k : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    have h1 := F.continuation.analyticAt_value_of_ne_one hk1
    have h2 : AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (u + (k + 1 : ℕ))) (-(k : ℂ)) := by
      have hre : 0 < (-(k : ℂ) + ((k + 1 : ℕ) : ℂ)).re := by push_cast; simp
      exact AnalyticAt.comp (g := Complex.Gamma) (f := fun u : ℂ => u + ((k + 1 : ℕ) : ℂ))
        (x := -(k : ℂ)) (HTGeometry.analyticAt_Gamma_of_re_pos hre) (by fun_prop)
    have h3 : AnalyticAt ℂ (fun u : ℂ => (∏ j ∈ Finset.range k, (u + j))⁻¹) (-(k : ℂ)) :=
      (Finset.analyticAt_fun_prod _ fun j _ => by fun_prop).inv hprod_ne
    exact ((analyticAt_cpow_neg hz _).mul h1).mul (h2.mul h3)
  have hf : ∀ᶠ u in 𝓝[≠] (-(k : ℂ)),
      ordinaryMellinIntegrand F 0 z u = G u / (u - (-(k : ℂ))) := by
    have hball : ∀ᶠ u in 𝓝 (-(k : ℂ)), dist u (-(k : ℂ)) < 1 / 2 :=
      Metric.eventually_nhds_iff.2 ⟨1 / 2, by norm_num, fun _ h => h⟩
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with u hu hune
    have hune' : u ≠ -(k : ℂ) := hune
    have hnz : ∀ j < k + 1, u + j ≠ 0 := by
      intro j hj h0
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | rfl
      · have heq : dist u (-(k : ℂ)) = ((k - j : ℕ) : ℝ) := by
          rw [Complex.dist_eq, show u - -(k : ℂ) = (u + j) + ((k - j : ℕ) : ℂ) by
            push_cast [Nat.cast_sub hjk.le]; ring, h0, zero_add, Complex.norm_natCast]
        rw [heq] at hu
        have : (1 : ℝ) ≤ ((k - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k - j)
        linarith
      · exact hune' (by linear_combination h0)
    have hΓ := Gamma_add_nat_eq_prod_mul u (k + 1) hnz
    rw [Finset.prod_range_succ] at hΓ
    have hpk : ∏ j ∈ Finset.range k, (u + j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => hnz j (by have := Finset.mem_range.1 hj; omega)
    have huk : u - -(k : ℂ) ≠ 0 := sub_ne_zero.2 hune'
    simp only [hGdef, ordinaryMellinIntegrand, zero_add]
    rw [hΓ, eq_div_iff huk, show u - -(k : ℂ) = u + k by ring]
    field_simp
  rw [laurentCoeff_neg_one_of_eq_div hG hf]
  simp only [hGdef]
  rw [show -(k : ℂ) + ((k + 1 : ℕ) : ℂ) = 1 by push_cast; ring, Complex.Gamma_one,
    one_mul, prod_range_neg_nat_add, neg_neg, Complex.cpow_natCast]
  have hsign : ((-1 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ = (-1) ^ k / (k.factorial : ℂ) := by
    rw [mul_inv, ← inv_pow, inv_neg, inv_one, div_eq_mul_inv]
  rw [hsign]
  ring

/-- The polar contribution is analytic away from the logarithm cut, including
neighbourhoods of every nonzero point of the imaginary axis. -/
theorem analyticOnNhd_ordinaryPolarPart (F : ExtendedSelbergClass) :
    AnalyticOnNhd ℂ (ordinaryPolarPart F) Complex.slitPlane := by
  set A : ℂ → ℂ := fun u => Complex.Gamma u * F u with hA
  have hAmero : MeromorphicAt A 1 := (Meromorphic.Gamma 1).mul (F.meromorphic_value 1)
  obtain ⟨k, hk1, hkB⟩ := exists_analyticAt_laurentShift_ge hAmero 1
  set B := laurentShift A 1 k with hBdef
  set β : ℕ → ℂ := fun j => iteratedDeriv j B 0 with hβ
  set Q : ℂ → ℂ := fun z => ((k - 1).factorial : ℂ)⁻¹ *
    ∑ i ∈ Finset.range k, ((k - 1).choose i : ℂ) *
      (Complex.exp (-Complex.log z) * (-Complex.log z) ^ i) * β (k - 1 - i) with hQ
  have hformula : ∀ z : ℂ, z ∈ Complex.slitPlane → ordinaryPolarPart F z = Q z := by
    intro z hz
    have hz0 := Complex.slitPlane_ne_zero hz
    set E : ℂ → ℂ := fun t => Complex.exp (-Complex.log z) *
      Complex.exp (-Complex.log z * t) with hE
    have hshift : laurentShift (ordinaryMellinIntegrand F 0 z) 1 k = fun t => E t * B t := by
      funext t
      simp only [laurentShift, hE, hBdef, ordinaryMellinIntegrand, hA, zero_add]
      rw [Complex.cpow_def_of_ne_zero hz0, ← Complex.exp_add]
      have he : Complex.log z * -(1 + t) = -Complex.log z + -Complex.log z * t := by ring
      rw [he]
      ring
    have hEan : AnalyticAt ℂ E 0 := by fun_prop
    have hana : AnalyticAt ℂ (laurentShift (ordinaryMellinIntegrand F 0 z) 1 k) 0 := by
      rw [hshift]
      exact hEan.mul hkB
    have hℓ : (0 : ℤ) ≤ -1 + (k : ℤ) := by omega
    rw [ordinaryPolarPart, laurentCoeff_eq_taylorCoeffZero hana hℓ, hshift]
    have hidx : ((-1 : ℤ) + (k : ℤ)).toNat = k - 1 := by omega
    rw [hidx, taylorCoeffZero]
    change iteratedDeriv (k - 1) (E * B) 0 / _ = _
    rw [iteratedDeriv_mul hEan.contDiffAt hkB.contDiffAt]
    have hEder : ∀ i : ℕ, iteratedDeriv i E 0 = Complex.exp (-Complex.log z) * (-Complex.log z) ^ i := by
      intro i
      have h1 : iteratedDeriv i E 0 = Complex.exp (-Complex.log z) *
          iteratedDeriv i (fun t => Complex.exp (-Complex.log z * t)) 0 :=
        iteratedDeriv_const_mul_field _ _
      rw [h1, iteratedDeriv_cexp_const_mul]
      simp
    simp_rw [hEder]
    rw [hQ, div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr (by rw [Nat.sub_add_cancel (by omega)]) fun i _ => ?_
    simp only [hβ]
  intro z hz
  have hlog := analyticAt_clog hz
  have hQan : AnalyticAt ℂ Q z := by
    simp only [hQ]
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => ?_)
    exact (analyticAt_const.mul ((hlog.neg.cexp).mul (hlog.neg.pow i))).mul analyticAt_const
  refine hQan.congr ?_
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
  exact (hformula w hw).symm

end GaloisForLFunctions.SelbergClass
