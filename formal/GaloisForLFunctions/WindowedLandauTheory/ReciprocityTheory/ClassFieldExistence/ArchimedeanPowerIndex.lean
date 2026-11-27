import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalPowerIndexProducts
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysFrobeniusRange

/-! Archimedean local power indices come from the real sign quotient.
In the presence of all n-th roots of unity, the real case has n at most two. -/

noncomputable section

open NumberField

namespace GlobalTheory.Reciprocity

private theorem exists_pos_real_pow_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : ℝ, 0 < y ∧ y ^ n = x :=
  ⟨x ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos hx _, Real.rpow_inv_natCast_pow hx.le hn⟩

private theorem mem_range_squareReal (x : ℝˣ) :
    x ∈ (powMonoidHom 2 : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact sq_pos_of_ne_zero y.ne_zero
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx (n := 2) (by decide)
    exact ⟨Units.mk0 y hy.ne', Units.ext hyx⟩

private theorem index_squareReal : (powMonoidHom 2 : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b => ?_⟩
  rw [mem_range_squareReal, mem_range_squareReal, Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · exact Or.inl ⟨neg_pos.mpr hb, hb.not_gt⟩
  · exact Or.inr ⟨hb, by linarith⟩

variable {K : Type*} [Field K]

theorem mem_range_power_infiniteCompletion (w : InfinitePlace K) (x : (w.Completion)ˣ)
    {n : ℕ} (hn : 0 < n)
    (hx : ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      (x : w.Completion)) :
    x ∈ (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv
    have h : 0 < (e x : ℝ) := hx hw
    obtain ⟨y, hy, he⟩ := exists_pos_real_pow_eq h hn.ne'
    refine ⟨e.symm (Units.mk0 y hy.ne'), e.injective ?_⟩
    rw [powMonoidHom_apply, map_pow, MulEquiv.apply_symm_apply]
    exact Units.ext he
  · let e := Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv
    obtain ⟨y, hy⟩ := RHTower.deningerUnitsPow_surjective hn (e x)
    refine ⟨e.symm y, e.injective ?_⟩
    rw [powMonoidHom_apply, map_pow, MulEquiv.apply_symm_apply]
    exact hy

variable {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem eq_one_or_eq_two_of_real_place {w : InfinitePlace K} (hw : w.IsReal) : n = 1 ∨ n = 2 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  let x := InfinitePlace.embedding_of_isReal hw ζ
  have h : IsPrimitiveRoot x n := hζ.map_of_injective (InfinitePlace.embedding_of_isReal hw).injective
  have habs : |x| = 1 := by
    have he : |x| ^ n = 1 := by rw [← abs_pow, h.pow_eq_one, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg x) (NeZero.ne n)).mp he
  have h₂ : x ^ 2 = 1 := by rw [← sq_abs, habs, one_pow]
  exact (Nat.dvd_prime Nat.prime_two).mp (h.dvd_of_pow_eq_one 2 h₂)

/-- Include the real norm with weight one and the complex norm with
weight two. The local power index then contributes a common n². -/
theorem index_power_infiniteCompletion_mul_norm (w : InfinitePlace K) :
    ((powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index : ℝ) *
      ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ 2 := by
  have hnorm : ‖(n : w.Completion)‖ = n := by
    rw [← map_natCast (algebraMap K w.Completion) n]
    change ‖((WithAbs.equiv w.1).symm (n : K) : w.Completion)‖ = n
    rw [InfinitePlace.Completion.norm_coe]
    exact (congrArg (fun x : K => w x) ((WithAbs.equiv w.1).apply_symm_apply (n : K))).trans
      (w.map_natCast n)
  rw [hnorm]
  rcases w.isReal_or_isComplex with hw | hw
  · let e := Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv
    rw [index_power_congr e n, show w.mult = 1 by simp [InfinitePlace.mult, hw], pow_one]
    rcases eq_one_or_eq_two_of_real_place (n := n) hw with h | h
    · subst n
      have h : (powMonoidHom 1 : ℝˣ →* ℝˣ).range = ⊤ :=
        MonoidHom.range_eq_top.mpr fun x => ⟨x, pow_one x⟩
      simp [h]
    · subst n
      rw [index_squareReal]
      norm_num
  · let e := Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv
    rw [index_power_congr e n, MonoidHom.range_eq_top.mpr (RHTower.deningerUnitsPow_surjective (NeZero.pos n)),
      Subgroup.index_top, show w.mult = 2 by simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw]]
    simp

end GlobalTheory.Reciprocity
