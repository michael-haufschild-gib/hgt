import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InertiaFixedPlaceSeparation

/-! Distinct extensions of a finite place have trivial common inertia.
An inertia-fixed separating coefficient gives a polynomial with at most
one root in each residue class. Its roots force the common inertia element
to fix every algebraic integer. -/

noncomputable section

open Polynomial IsLocalRing NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaLift

private theorem eq_of_perturbed_pow_sub_one {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] (y z u : R) (m : ℕ) (h : ℤ[X])
    (hy : y ^ m - 1 = u * aeval y h) (hz : z ^ m - 1 = u * aeval z h)
    (hu : u ∈ maximalIdeal R) (hzy : z - y ∈ maximalIdeal R)
    (hm : (m : R) ∉ maximalIdeal R) : z = y := by
  by_contra hne
  obtain ⟨k, hk⟩ : z - y ∣ aeval z h - aeval y h := by
    simpa only [eval_map_algebraMap] using sub_dvd_eval_sub z y (h.map (algebraMap ℤ R))
  have hS : (∑ i ∈ Finset.range m, z ^ i * y ^ (m - 1 - i)) = u * k := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    rw [Commute.geom_sum₂_mul (Commute.all z y)]
    linear_combination hz - hy + u * hk
  have hu₀ : residue R u = 0 := (residue_eq_zero_iff _).mpr hu
  have hzy₀ : residue R z = residue R y := by
    have he := (residue_eq_zero_iff _).mpr hzy
    rwa [map_sub, sub_eq_zero] at he
  have hm₀ : (m : ResidueField R) ≠ 0 := by
    intro h
    apply hm
    rw [← residue_eq_zero_iff, map_natCast, h]
  have hmn : m ≠ 0 := by rintro rfl; exact hm₀ (by simp)
  have hyp : (residue R y) ^ m = 1 := by
    have he := congrArg (residue R) hy
    rwa [map_sub, map_mul, hu₀, zero_mul, map_pow, map_one, sub_eq_zero] at he
  have hy₀ : residue R y ≠ 0 := by
    intro h
    rw [h, zero_pow hmn] at hyp
    exact zero_ne_one hyp
  have he := congrArg (residue R) hS
  simp only [map_sum, map_mul, map_pow, hu₀, zero_mul, hzy₀] at he
  rw [geom_sum₂_self] at he
  exact mul_ne_zero hm₀ (pow_ne_zero _ hy₀) he

/-- Perturbing a monic integral polynomial by a fixed coefficient congruent to
one gives integral roots fixed by inertia and a product identity at its old root. -/
theorem exists_inertia_fixed_polynomial_roots {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (b e : Ω) (m : ℕ) (f : ℤ[X])
    (he : IsIntegral ℤ e) (hσe : σ e = e) (hv : A.valuation (1 - e) < 1)
    (hm : A.valuation (m : Ω) = 1) (hf : f.Monic) (hfm : f.natDegree = m) (hb : aeval b f = 0) :
    ∃ ys : Multiset Ω, ys.card = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧
      e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hm₀ : m ≠ 0 := by rintro rfl; simp at hm
  let h : ℤ[X] := X ^ m - C 1 - f
  have hdeg : h.degree < (m : WithBot ℕ) := by
    have hmX : (X ^ m - C 1 : ℤ[X]).Monic := monic_X_pow_sub_C 1 hm₀
    have hXd : (X ^ m - C 1 : ℤ[X]).degree = m := degree_X_pow_sub_C (Nat.pos_of_ne_zero hm₀) 1
    have hfd : f.degree = m := by rw [degree_eq_natDegree hf.ne_zero, hfm]
    rw [← hXd]
    exact degree_sub_lt (hXd.trans hfd.symm) hmX.ne_zero (by rw [hmX.leadingCoeff, hf.leadingCoeff])
  let R := integralClosure ℤ Ω
  let e₀ : R := ⟨e, he⟩
  let g₀ : R[X] := f.map (algebraMap ℤ R) + C e₀ * h.map (algebraMap ℤ R)
  have hfd : (f.map (algebraMap ℤ R)).degree = m := by
    rw [hf.degree_map, degree_eq_natDegree hf.ne_zero, hfm]
  have hlt : (C e₀ * h.map (algebraMap ℤ R)).degree < (f.map (algebraMap ℤ R)).degree := by
    rw [hfd, ← smul_eq_C_mul]
    exact lt_of_le_of_lt ((degree_smul_le _ _).trans degree_map_le) hdeg
  have hg₀ : g₀.Monic := (hf.map _).add_of_left hlt
  have hg₀d : g₀.degree = m := (degree_add_eq_left_of_degree_lt hlt).trans hfd
  have heval (y : Ω) : aeval y g₀ = aeval y f + e * aeval y h := by
    simp only [g₀, map_add, map_mul, aeval_map_algebraMap, aeval_C]
    rfl
  have heval' (y : Ω) : aeval y h = y ^ m - 1 - aeval y f := by simp [h]
  let g := g₀.map (algebraMap R Ω)
  have hg : g.Monic := hg₀.map _
  have hgd : g.natDegree = m := by
    rw [hg₀.natDegree_map, natDegree_eq_of_degree_eq_some hg₀d]
  have hcard : g.roots.card = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨g.roots, hcard.trans hgd, ?_, ?_⟩
  · intro y hy
    have hy₀ : aeval y g₀ = 0 := by
      have hr := (mem_roots hg.ne_zero).mp hy
      change (g₀.map (algebraMap R Ω)).eval y = 0 at hr
      rwa [eval_map_algebraMap] at hr
    have hint : IsIntegral ℤ y := isIntegral_trans y (show IsIntegral R y from ⟨g₀, hg₀, hy₀⟩)
    refine ⟨hint, ?_⟩
    have hyA : y ∈ A := mem_of_isIntegral_int A hint
    have hzA : σ y ∈ A := (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hσ) y).mpr hyA
    have huA : 1 - e ∈ A := (A.valuation_le_one_iff _).mp hv.le
    have hrel : y ^ m - 1 = (1 - e) * aeval y h := by
      rw [heval] at hy₀
      linear_combination hy₀ - heval' y
    have hrelσ : (σ y) ^ m - 1 = (1 - e) * aeval (σ y) h := by
      have hmapped := congrArg σ hrel
      rw [map_sub, map_pow, map_one, map_mul, map_sub, map_one, hσe] at hmapped
      rw [hmapped]
      congr 1
      exact (aeval_algHom_apply (σ : Ω →+* Ω).toIntAlgHom y h).symm
    have hae (x : A) : ((aeval x h : A) : Ω) = aeval (x : Ω) h :=
      (aeval_algHom_apply A.subtype.toIntAlgHom x h).symm
    have hfix := eq_of_perturbed_pow_sub_one (R := A) ⟨y, hyA⟩ ⟨σ y, hzA⟩ ⟨1 - e, huA⟩ m h
      (Subtype.ext (by simpa [hae] using hrel)) (Subtype.ext (by simpa [hae] using hrelσ))
      ((A.valuation_lt_one_iff _).mpr hv)
      ((A.valuation_lt_one_iff _).mpr (hσ.2 y ((A.valuation_le_one_iff _).mpr hyA)))
      (fun hmA => by
        have hlt := (A.valuation_lt_one_iff _).mp hmA
        rw [show ((m : A) : Ω) = m by simp, hm] at hlt
        exact lt_irrefl 1 hlt)
    exact congrArg Subtype.val hfix
  · calc
      e * (b ^ m - 1) = g.eval b := by
        change e * (b ^ m - 1) = (g₀.map (algebraMap R Ω)).eval b
        rw [eval_map_algebraMap, heval, heval', hb, zero_add, sub_zero]
      _ = (g.roots.map (fun y => b - y)).prod := by
        have he := congrArg (Polynomial.eval b) ((IsAlgClosed.splits g).eq_prod_roots_of_monic hg)
        simpa only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
          eval_sub, eval_X, eval_C] using he

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

private theorem eq_one_of_fixes_integral (σ : G E Ω)
    (hσ : ∀ b : Ω, IsIntegral ℤ b → σ b = b) : σ = 1 := by
  ext x
  obtain ⟨s, t, hs, ht, hs₁, hst⟩ := exists_den E (⊤ : ValuationSubring Ω) (x := x)
    ((ValuationSubring.valuation_le_one_iff _ _).mpr trivial)
  have hs₀ : s ≠ 0 := by rintro rfl; simp at hs₁
  have h := congrArg σ hst
  rw [map_mul, hσ s hs, hσ t ht, ← hst] at h
  exact mul_left_cancel₀ hs₀ h

private theorem exists_ge_valuation_nat_eq_one (B : ValuationSubring Ω) {p : ℕ} [Fact p.Prime]
    (hp : B.valuation (p : Ω) < 1) (d : ℕ) :
    ∃ m : ℕ, d ≤ m ∧ B.valuation (m : Ω) = 1 := by
  have hprime : p.Prime := Fact.out
  have h (m : ℕ) (hm : ¬ p ∣ m) : B.valuation (m : Ω) = 1 :=
    le_antisymm (valuation_natCast_le_one B m) (le_of_not_gt
      (GlobalTheory.TameKummer.natCast_valuation_not_lt_one B hp (hprime.coprime_iff_not_dvd.mpr hm)))
  by_cases hd : p ∣ d
  · refine ⟨d + 1, Nat.le_succ d, h _ (fun hd₁ => ?_)⟩
    exact hprime.not_dvd_one (by simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hd₁ hd)
  · exact ⟨d, le_rfl, h d hd⟩

/-- Nontrivial common inertia determines a unique valuation above a fixed finite place. -/
theorem eq_of_nontrivial_common_inertia (A B : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver A v) (hB : IsPlaceOver B v)
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝓞 E) ∈ v.asIdeal) {σ : G E Ω}
    (hσA : σ ∈ Ine (F := E) A) (hσB : σ ∈ Ine (F := E) B) (hσ : σ ≠ 1) : A = B := by
  by_contra hAB
  apply hσ
  apply eq_one_of_fixes_integral
  intro b hb
  by_contra hne
  have hpA : A.valuation (p : Ω) < 1 := by simpa using (hA (p : 𝓞 E)).mpr hp
  have hpB : B.valuation (p : Ω) < 1 := by simpa using (hB (p : 𝓞 E)).mpr hp
  let f := minpoly ℤ b
  have hf : f.Monic := minpoly.monic hb
  obtain ⟨m, hm, hmB⟩ := exists_ge_valuation_nat_eq_one B hpB f.natDegree
  let g := X ^ (m - f.natDegree) * f
  have hg : g.Monic := (monic_X_pow _).mul hf
  have hgd : g.natDegree = m := by
    rw [show g = X ^ (m - f.natDegree) * f from rfl,
      (monic_X_pow _).natDegree_mul hf, natDegree_X_pow, Nat.sub_add_cancel hm]
  have hgb : aeval b g = 0 := by simp [g, f, minpoly.aeval]
  have hc : IsIntegral ℤ ((σ b - b) ^ m) :=
    (((hb.map (σ : Ω →+* Ω).toIntAlgHom).sub hb)).pow m
  have hc₀ : (σ b - b) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
  obtain ⟨e, he, hσe, hsmall, heB⟩ :=
    exists_inertia_fixed_integral_separator A B v hA hB hAB hpA hσB hc hc₀
  obtain ⟨ys, hys, hfix, hprod⟩ := exists_inertia_fixed_polynomial_roots B hσB b e m g
    he hσe heB hmB hg hgd hgb
  have hbound₁ : A.valuation (e * (b ^ m - 1)) < A.valuation (σ b - b) ^ m := by
    have hle := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ((hb.pow m).sub isIntegral_one))
    rw [map_mul, ← map_pow]
    exact (mul_le_of_le_one_right' hle).trans_lt hsmall
  have hbound₂ : A.valuation (σ b - b) ^ m ≤ A.valuation ((ys.map (fun y => b - y)).prod) := by
    rw [map_multiset_prod, Multiset.map_map, ← hys]
    rw [← Multiset.card_map (fun y => A.valuation (b - y)) ys]
    apply Multiset.pow_card_le_prod
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hfixy := (hfix y hy).2
    have heq : σ b - b = σ (b - y) - (b - y) := by rw [map_sub, hfixy]; ring
    rw [heq]
    refine (Valuation.map_sub _ _ _).trans ?_
    rw [valuation_apply_eq_of_mem_Dec A (Ine_le_Dec A hσA), max_self]
  rw [← hprod] at hbound₂
  exact (not_le_of_gt hbound₁) hbound₂

end GlobalTheory.InertiaLift
