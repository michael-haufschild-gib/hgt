import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The covolume of an ideal in a quadratic complex field scales by its absolute norm. -/

open NumberField Module

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

theorem place_unique [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (v w : InfinitePlace K) : v = w := by
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, h2] at hr
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at hc
  have h1 : Fintype.card (InfinitePlace K) = 1 := by omega
  exact Fintype.card_le_one_iff.1 h1.le v w

theorem normSq_eq [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast

theorem finite_units [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) : Finite (𝓞 K)ˣ := by
  have hfin := Embeddings.finite_of_norm_le K ℂ 1
  have hone : ∀ (u : (𝓞 K)ˣ) (ψ : K →+* ℂ), ‖ψ ((u : 𝓞 K) : K)‖ = 1 := by
    intro u ψ
    have h := normSq_eq h2 ψ (u : 𝓞 K)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  haveI := hfin.to_subtype
  refine Finite.of_injective (fun u : (𝓞 K)ˣ =>
    (⟨((u : 𝓞 K) : K), (u : 𝓞 K).isIntegral_coe, fun ψ => (hone u ψ).le⟩ :
      {x : K | IsIntegral ℤ x ∧ ∀ ψ : K →+* ℂ, ‖ψ x‖ ≤ 1})) ?_
  intro u v huv
  exact Units.ext (RingOfIntegers.ext (by simpa using congrArg Subtype.val huv))

theorem im_ne_zero [IsTotallyComplex K] (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ≠ 0 := by
  intro him
  have h2 : Module.finrank ℚ K = 2 := by
    rw [← RingOfIntegers.rank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (RingOfIntegers.ext (by simpa using h))
  have ha0 : φ (b 0 : K) ≠ 0 := (map_ne_zero φ).2 hb0
  have hca0 : starRingEnd ℂ (φ (b 0 : K)) ≠ 0 := (map_ne_zero _).2 ha0
  set y : K := (b 1 : K) / (b 0 : K) with hy
  have hφy : (φ y).im = 0 := by
    have hq : φ y = (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)) /
        (Complex.normSq (φ (b 0 : K)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_div_mul_left _ _ hca0, hy, map_div₀]
    rw [hq, Complex.div_ofReal_im, him, zero_div]
  by_cases hyq : y ∈ Set.range (algebraMap ℚ K)
  · obtain ⟨q, hq⟩ := hyq
    have hK : (q.den : K) * (b 1 : K) = (q.num : K) * (b 0 : K) := by
      have hd : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
      have h1 : (b 1 : K) = (q : K) * (b 0 : K) := by
        rw [← eq_ratCast (algebraMap ℚ K) q, hq, hy, div_mul_cancel₀ _ hb0]
      rw [h1, Rat.cast_def]
      field_simp
    have hz : (-q.num) • b 0 + ((q.den : ℤ)) • b 1 = 0 := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap] at hK ⊢
      simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, map_neg, map_zero, map_natCast]
      push_cast at hK ⊢
      linear_combination hK
    have := Fintype.linearIndependent_iff.1 b.linearIndependent ![-q.num, (q.den : ℤ)]
      (by simpa [Fin.sum_univ_two] using hz) 1
    simp at this
  · have hli : LinearIndependent ℚ ![(1 : K), y] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have hg1 : g 1 = 0 := by
        by_contra hne
        apply hyq
        refine ⟨-(g 0) / g 1, ?_⟩
        rw [eq_ratCast]
        push_cast
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hg
        rw [div_eq_iff (by exact_mod_cast hne)]
        linear_combination -hg
      have hg0 : g 0 = 0 := by
        rw [hg1, zero_smul, add_zero, smul_eq_zero] at hg
        simpa using hg
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
    have hreal : ∀ x : K, (φ x).im = 0 := by
      intro x
      have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), y]) := htop ▸ Submodule.mem_top
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
      simp [Fin.sum_univ_two, Rat.smul_def, hφy]
    have hR : ComplexEmbedding.IsReal φ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.2 (hreal x)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex
      (InfinitePlace.mk φ))) (InfinitePlace.isReal_mk_iff.2 hR)

theorem abs_im_eq (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (J : Ideal (𝓞 K))
    (e : Module.Basis (Fin 2) ℤ J) :
    |(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| =
      Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by
  classical
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef
  have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl
  have he : ∀ j, ψ (e j : 𝓞 K) = (b.repr (e j : 𝓞 K) 0 : ℂ) * ψ (b 0) +
      (b.repr (e j : 𝓞 K) 1 : ℂ) * ψ (b 1) := by
    intro j
    conv_lhs => rw [← b.sum_repr (e j : 𝓞 K)]
    simp [Fin.sum_univ_two, zsmul_eq_mul]
  have hdet := Ideal.natAbs_det_basis_change b J e
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at hdet
  simp only [hψ]
  rw [← hdet, Nat.cast_natAbs, Int.cast_abs, ← abs_mul, he 0, he 1]
  congr 1
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

end GlobalTheory.Mem.PartialZeta
