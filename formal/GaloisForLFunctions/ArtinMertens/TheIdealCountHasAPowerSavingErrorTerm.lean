import GaloisForLFunctions.ArtinMertens.TheFrontierOfTheNormBallIsLipschitz
import GaloisForLFunctions.ArtinMertens.TheSoftMertensTheoremForPrimeIdeals

/-!
# The ideal count has a power-saving error term

For a number field `K` of degree `n`, the number of non-zero ideals of norm `≤ s` is
`I_K(s) = c_K s + O(s^{1−1/n})`, `c_K` the residue of the Dedekind zeta function
(`exists_abs_card_norm_le_sub_le`, `exists_abs_idealCount_sub_le`). This is Weber's theorem.

* **Classes** (`card_norm_le_eq_sum_class`, `card_class_eq_card_principal`): the ideals of a class
  `C` and norm `≤ s` correspond to the principal multiples of `J` (`[J] = C⁻¹`) of norm `≤ s N(J)`,
  and these, times the torsion order, to the points of the lattice `Λ_J` in the cone with norm
  `≤ s N(J)` (Mathlib's `card_isPrincipal_dvd_norm_le`, `card_idealSet_norm_le_eq`).
* **Dilates** (`setOf_norm_le_eq_smul`): `{x ∈ cone : N(x) ≤ T} = T^{1/n} · normLeOne`.
* **Lattice count**: the frontier of `normLeOne` is Lipschitz (`frontier_normLeOne_subset`), so
  `#(tY ∩ Λ_J) covol(Λ_J) = tⁿ vol(Y) + O(tⁿ⁻¹)` (`exists_abs_ncard_smul_sub_le`) with
  `t = (s N(J))^{1/n}`, `tⁿ⁻¹ = (s N(J))^{1−1/n}`.
* **The constant** is `c_K` since `I_K(s)/s → c_K` (`tendsto_norm_le_div_atTop₀`).
-/

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units Set MeasureTheory Filter Topology Ideal Module
open scoped Classical NNReal nonZeroDivisors Pointwise

namespace GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K]

local notation "n" => finrank ℚ K

/-- The ideals of class `C` and norm `≤ s` correspond to the principal multiples of `J`,
`[J] = C⁻¹`, of norm `≤ s N(J)`. -/
theorem card_class_eq_card_principal {C : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰}
    (hJ : ClassGroup.mk0 J = C⁻¹) (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} =
      Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧
        Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ ↦
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm

/-- The points of `idealSet K J` of norm `≤ T` are the lattice points of `Λ_J` in the cone with
norm `≤ T`. -/
theorem card_idealSet_norm_le_eq (J : (Ideal (𝓞 K))⁰) (T : ℝ) :
    Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ T} =
      ({x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ T} ∩
        (idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K))).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ idealSet K J)
    fun x => mixedEmbedding.norm x ≤ T).trans (Equiv.subtypeEquivRight fun x => ?_))
  simp only [mem_idealSet, mem_inter_iff, mem_setOf_eq, SetLike.mem_coe, mem_idealLattice,
    FractionalIdeal.coe_mk0, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨⟨hx, a, ha, rfl⟩, hT⟩
    exact ⟨⟨hx, hT⟩, _, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨⟨hx, hT⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨⟨hx, a, ha, rfl⟩, hT⟩

/-- **Dilates**: `{x ∈ cone : N(x) ≤ T} = T^{1/n} · normLeOne`. -/
theorem setOf_norm_le_eq_smul {T : ℝ} (hT : 0 < T) :
    {x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ T} =
      (T ^ ((n : ℝ)⁻¹)) • normLeOne K := by
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  have ht : 0 < T ^ ((n : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  have htn : (T ^ ((n : ℝ)⁻¹)) ^ n = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le, inv_mul_cancel₀ hn.ne', Real.rpow_one]
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_setOf_eq, mem_inter_iff, mem_setOf_eq,
    smul_mem_iff_mem (inv_ne_zero ht.ne'), mixedEmbedding.norm_smul, abs_inv, abs_of_pos ht,
    inv_pow, htn, inv_mul_le_iff₀ hT, mul_one]

/-- The ideals of norm `≤ s` split over the ideal classes. -/
theorem card_norm_le_eq_sum_class {s : ℝ} (hs : 0 ≤ s) :
    (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) =
      ∑ C : ClassGroup (𝓞 K), (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) := by
  have : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} := by
    simp_rw [← Nat.le_floor_iff hs]
    exact @Fintype.ofFinite _ (finite_setOf_absNorm_le₀ ⌊s⌋₊)
  let e := fun C : ClassGroup (𝓞 K) ↦ Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm I.1 ≤ s) (fun I ↦ ClassGroup.mk0 I = C)
  simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := fun I ↦ ClassGroup.mk0 I.1)
    (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Nat.cast_sum]

/-- **The lattice count in dilates of `normLeOne`**: for every ideal `J`,
`|#(t·normLeOne ∩ Λ_J) covol(Λ_J) − tⁿ vol(normLeOne)| ≤ C tⁿ⁻¹` for `t ≥ 1`. -/
theorem exists_abs_ncard_smul_normLeOne_sub_le (J : (Ideal (𝓞 K))⁰) :
    ∃ C₁ : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(((t • normLeOne K) ∩ (idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K))).ncard
          : ℝ) * ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J))
            (volume : Measure (mixedSpace K)) -
        t ^ n * (volume : Measure (mixedSpace K)).real (normLeOne K)| ≤ C₁ * t ^ (n - 1) := by
  obtain ⟨M, hM⟩ := exists_lipschitzOnWith_boundaryParam (K := K)
  have h := exists_abs_ncard_smul_sub_le (volume : Measure (mixedSpace K))
    (idealLattice K (FractionalIdeal.mk0 K J)) (card_paramIndex K)
    (φ := fun j : ({w : InfinitePlace K // IsReal w} → Bool) × paramIndex K × Bool =>
      boundaryParam j.1) (fun j => hM j.1) (fun j => j.2.1)
    (c := fun j => if j.2.2 then 1 else 0) (fun j => by split_ifs <;> simp)
    (isBounded_normLeOne K) (frontier_normLeOne_subset (K := K))
  rwa [mixedEmbedding.finrank K] at h

/-- The class count times the torsion order is the lattice count in `(s N(J))^{1/n}·normLeOne`. -/
theorem card_class_mul_torsionOrder_eq {C : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰}
    (hJ : ClassGroup.mk0 J = C⁻¹) {s : ℝ} (hs : 0 < s) :
    (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧
      ClassGroup.mk0 I = C} : ℝ) * torsionOrder K =
      ((((s * absNorm (J : Ideal (𝓞 K))) ^ ((n : ℝ)⁻¹)) • normLeOne K) ∩
        (idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K))).ncard := by
  have hT : 0 < s * absNorm (J : Ideal (𝓞 K)) :=
    mul_pos hs (by exact_mod_cast absNorm_pos_of_nonZeroDivisors J)
  rw [card_class_eq_card_principal hJ s, ← Nat.cast_mul, card_isPrincipal_dvd_norm_le,
    card_idealSet_norm_le_eq, setOf_norm_le_eq_smul hT]

/-- Dividing a lattice-count estimate by `covol · torsion`. -/
theorem abs_sub_le_of_abs_mul_sub_le {X a T v q C₁ E : ℝ} (hq : 0 < q) (hT : T = a * q / v)
    (hv : 0 < v) (h : |X * v - T * q| ≤ C₁ * E) : |X - a * q / v * 1| ≤ C₁ / v * E := by
  sorry

/-- **Weber's theorem for one ideal class**: `#{I ∈ C : N I ≤ s} = a_C s + O(s^{1−1/n})`. -/
theorem exists_abs_card_class_sub_le (C : ClassGroup (𝓞 K)) :
    ∃ a B : ℝ, ∀ s : ℝ, 1 ≤ s →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧
        ClassGroup.mk0 I = C} : ℝ) - a * s| ≤ B * s ^ (1 - (n : ℝ)⁻¹) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨C₁, hC₁⟩ := exists_abs_ncard_smul_normLeOne_sub_le (K := K) J
  have hNJ1 : (1 : ℝ) ≤ absNorm (J : Ideal (𝓞 K)) := by
    exact_mod_cast absNorm_pos_of_nonZeroDivisors J
  have hcov0 : 0 < ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J))
      (volume : Measure (mixedSpace K)) := ZLattice.covolume_pos _ _
  have htor0 : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  have hn1 : (1 : ℕ) ≤ n := finrank_pos
  refine ⟨(absNorm (J : Ideal (𝓞 K)) : ℝ) * (volume : Measure (mixedSpace K)).real (normLeOne K) /
      (ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume * torsionOrder K),
    C₁ * (absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (1 - (n : ℝ)⁻¹) /
      (ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume * torsionOrder K),
    fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have hT0 : 0 < s * absNorm (J : Ideal (𝓞 K)) := by positivity
  have ht1 : 1 ≤ (s * absNorm (J : Ideal (𝓞 K))) ^ ((n : ℝ)⁻¹) :=
    Real.one_le_rpow (by nlinarith) (by positivity)
  have htn : ((s * absNorm (J : Ideal (𝓞 K))) ^ ((n : ℝ)⁻¹)) ^ n =
      s * absNorm (J : Ideal (𝓞 K)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, inv_mul_cancel₀ hn.ne', Real.rpow_one]
  have htn1 : ((s * absNorm (J : Ideal (𝓞 K))) ^ ((n : ℝ)⁻¹)) ^ (n - 1) =
      s ^ (1 - (n : ℝ)⁻¹) * (absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (1 - (n : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, Nat.cast_sub hn1, Nat.cast_one,
      show (n : ℝ)⁻¹ * ((n : ℝ) - 1) = 1 - (n : ℝ)⁻¹ by field_simp,
      Real.mul_rpow hs0.le (by positivity)]
  have h := hC₁ _ ht1
  rw [htn, htn1, ← card_class_mul_torsionOrder_eq hJ hs0] at h
  sorry

/-- **Weber's theorem**: `I_K(s) = c_K s + O(s^{1−1/n})`, `c_K` the residue of `ζ_K`. -/
theorem exists_abs_card_norm_le_sub_le :
    ∃ B : ℝ, ∀ s : ℝ, 1 ≤ s →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) -
        dedekindZeta_residue K * s| ≤ B * s ^ (1 - (n : ℝ)⁻¹) := by
  choose a B hB using exists_abs_card_class_sub_le (K := K)
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  -- a power saving with the constant `Σ_C a_C`
  have hsum : ∀ s : ℝ, 1 ≤ s →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) -
        (∑ C, a C) * s| ≤ (∑ C, B C) * s ^ (1 - (n : ℝ)⁻¹) := by
    intro s hs
    rw [card_norm_le_eq_sum_class (by linarith), Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun C _ => hB C s hs)
  -- the constant is the residue: `I_K(s)/s` tends to both
  have hlim : Tendsto (fun s : ℝ =>
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
        (𝓝 (∑ C, a C)) := by
    have hdec : Tendsto (fun s : ℝ => (∑ C, B C) * s ^ (-(n : ℝ)⁻¹)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := (n : ℝ)⁻¹) (by positivity)).const_mul (∑ C, B C)
      rwa [mul_zero] at this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdec
    filter_upwards [eventually_ge_atTop 1] with s hs
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs, show (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s - ∑ C, a C =
        ((Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) -
          (∑ C, a C) * s) / s by field_simp, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    calc _ ≤ (∑ C, B C) * s ^ (1 - (n : ℝ)⁻¹) := hsum s hs
      _ = (∑ C, B C) * s ^ (-(n : ℝ)⁻¹) * s := by
          rw [mul_assoc, ← Real.rpow_add_one hs0.ne', sub_eq_neg_add]
  have hc : ∑ C, a C = dedekindZeta_residue K :=
    tendsto_nhds_unique hlim (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K)
  exact ⟨∑ C, B C, fun s hs => hc ▸ hsum s hs⟩

/-- **Weber's theorem for `I_K`**: `|I_K(t) − c_K t| ≤ B t^{1−1/n}` for `t ≥ 1`. -/
theorem exists_abs_idealCount_sub_le :
    ∃ B : ℝ, ∀ t : ℕ, 1 ≤ t →
      |idealCount K t - dedekindZeta_residue K * t| ≤ B * (t : ℝ) ^ (1 - (n : ℝ)⁻¹) := by
  obtain ⟨B, hB⟩ := exists_abs_card_norm_le_sub_le (K := K)
  exact ⟨B, fun t ht => by
    rw [idealCount_eq]
    exact hB t (by exact_mod_cast ht)⟩

end GaloisForLFunctions.ArtinMertens
