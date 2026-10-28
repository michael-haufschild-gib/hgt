import GaloisForLFunctions.HeckeLFunctions.ConePointsOfARayClassAreLatticeCosets

/-!
# Ideals are equidistributed in ray classes

* **Equidistribution** (`exists_abs_ncard_rayClassIdeals_sub_le`): every ray class has the same
  density, `#{𝔞 ∈ c : N𝔞 ≤ x} = κ_𝔪 x + O(x^{1−1/n})`. By
  `ncard_rayClassIdeals_mul_torsionOrder_eq_sum` the count times `w` is a sum, over the data `g`
  above `c [𝔟]`, of lattice counts of `Λ_{𝔪₀𝔟}` in translated dilates `T^{1/n} Y_σ`, `T = x N𝔟`.
  Each is `T vol(Y)/covol + O(T^{1−1/n})` with `vol(Y_σ)` independent of `σ`, the number of `g`
  is the same for every class (`card_dataFiber`), and `covol(Λ_{𝔪₀𝔟}) ∝ N𝔪₀ N𝔟` cancels `N𝔟`.
* **Hecke character sums** (`exists_norm_sum_heckeCoeff_le`): for `ψ ≠ 1`,
  `Σ_{N𝔞 ≤ x} ψ(𝔞) = Σ_c ψ(c) #{𝔞 ∈ c : N𝔞 ≤ x} = O(x^{1−1/n})` since `Σ_c ψ(c) = 0`.
-/

noncomputable section

open MeasureTheory NumberField IsDedekindDomain FractionalIdeal Set NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Module NumberField.InfinitePlace
open scoped Classical nonZeroDivisors Pointwise

namespace GaloisForLFunctions.HeckeLFunctions

open GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The common density of the ray classes,
`κ_𝔪 = #(data over 1) · vol(Y_σ) / (w · N𝔪₀ · 2^{−r₂} √|d_K|)`. -/
def rayDensity : ℝ :=
  (dataFiber 𝔪 1).card * volume.real (signedNormBall 𝔪.inf (1 : 𝔪.inf → ℤˣ)) /
    (torsionOrder K * (Ideal.absNorm 𝔪.fin * ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|)))

variable {𝔪}

/-- Every class of principal ray classes carries the same number of data `g`. -/
theorem card_dataFiber {d : RayClassGroup 𝔪} (hd : toClassGroup 𝔪 d = 1) :
    (dataFiber 𝔪 d).card = (dataFiber 𝔪 1).card := by
  have hd' : d ∈ Set.range (rayResidueClass 𝔪) := by
    have : d ∈ (rayResidueClass 𝔪).range := by
      rw [range_rayResidueClass]
      exact hd
    exact MonoidHom.mem_range.mp this
  unfold dataFiber
  convert MonoidHom.card_fiber_eq_of_mem_range (rayResidueClass 𝔪) hd' ⟨1, map_one _⟩

/-- Summing `|N_i a − b| ≤ C_i e` over `i ∈ s`. -/
theorem abs_sum_mul_sub_le {ι : Type*} (s : Finset ι) (N C : ι → ℝ) {a b e : ℝ} (he : 0 ≤ e)
    (h : ∀ i ∈ s, |N i * a - b| ≤ C i * e) :
    |(∑ i ∈ s, N i) * a - s.card * b| ≤ (∑ i ∈ s, |C i|) * e := by
  rw [Finset.sum_mul, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi =>
    (h i hi).trans (mul_le_mul_of_nonneg_right (le_abs_self _) he))

/-- **One ray class**: `#{𝔞 ∈ c : N𝔞 ≤ x} = κ_𝔪 x + O(x^{1−1/n})`. -/
theorem exists_abs_ncard_rayClassIdeals_sub_le_of_class (c : RayClassGroup 𝔪) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x| ≤
        C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨𝔟, h𝔟0, h𝔟, h𝔟c⟩ := exists_integral_rep 𝔪 (toClassGroup 𝔪 c)⁻¹
  set Λ := idealLattice K (idealUnit (mul_ne_zero 𝔪.fin_ne_bot h𝔟0))
  set r := rayClass 𝔪 ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩
  set V := volume.real (signedNormBall 𝔪.inf (1 : 𝔪.inf → ℤˣ))
  set α := 1 - (finrank ℚ K : ℝ)⁻¹
  choose C hC using fun g : (rayHom 𝔪).range =>
    exists_abs_ncard_vadd_signedNormBall_sub_le Λ 𝔪.inf g.1.2
  -- the data above `c [𝔟]` are as many as the data above `1`
  have hcr : toClassGroup 𝔪 (c * r) = 1 := by
    rw [map_mul, toClassGroup_rayClass]
    exact (congrArg (_ * ·) h𝔟c).trans (mul_inv_cancel _)
  have hF : (dataFiber 𝔪 (c * r)).card = (dataFiber 𝔪 1).card := card_dataFiber hcr
  have hN𝔟1 : (1 : ℝ) ≤ Ideal.absNorm 𝔟 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hN𝔟 : (0 : ℝ) < Ideal.absNorm 𝔟 := by linarith
  have hcov0 : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos _ _
  have htor0 : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  have hcov : ZLattice.covolume Λ volume = Ideal.absNorm 𝔪.fin * Ideal.absNorm 𝔟 *
      ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) := by
    rw [covolume_idealLattice, coe_idealUnit, coeIdeal_absNorm, map_mul]
    push_cast
    ring
  refine ⟨(∑ g, |C g|) * (Ideal.absNorm 𝔟 : ℝ) ^ α / (ZLattice.covolume Λ volume * torsionOrder K),
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT : 1 ≤ x * (Ideal.absNorm 𝔟 : ℝ) := one_le_mul_of_one_le_of_one_le hx hN𝔟1
  -- sum the lattice-coset estimates over the data above `c [𝔟]`
  have h := abs_sum_mul_sub_le (dataFiber 𝔪 (c * r))
    (fun g => ((((-mixedEmbedding K (residueRep 𝔪 h𝔟 g.1.1 : K)) +ᵥ
      ((x * Ideal.absNorm 𝔟) ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall 𝔪.inf g.1.2) ∩
        (Λ : Set (mixedSpace K))).ncard : ℝ)) C (a := ZLattice.covolume Λ volume)
    (b := x * Ideal.absNorm 𝔟 * V) (Real.rpow_nonneg (by positivity) α) fun g _ => by
      have := hC g _ hT (-mixedEmbedding K (residueRep 𝔪 h𝔟 g.1.1 : K))
      rwa [measureReal_signedNormBall_eq 𝔪.inf g.1.2 1] at this
  have hsum := ncard_rayClassIdeals_mul_torsionOrder_eq_sum h𝔟0 h𝔟 h𝔟c hx0
  have hsumR : ((rayClassIdeals 𝔪 c x).ncard : ℝ) * torsionOrder K =
      ∑ g ∈ dataFiber 𝔪 (c * r), ((((-mixedEmbedding K (residueRep 𝔪 h𝔟 g.1.1 : K)) +ᵥ
        ((x * Ideal.absNorm 𝔟) ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall 𝔪.inf g.1.2) ∩
          (Λ : Set (mixedSpace K))).ncard : ℝ) := by
    exact_mod_cast hsum
  rw [← hsumR, hF, Real.mul_rpow hx0.le hN𝔟.le] at h
  have hCs : ∑ g ∈ dataFiber 𝔪 (c * r), |C g| ≤ ∑ g, |C g| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun g _ _ => abs_nonneg _
  have h' : |((rayClassIdeals 𝔪 c x).ncard : ℝ) * torsionOrder K * ZLattice.covolume Λ volume -
      x * Ideal.absNorm 𝔟 * ((dataFiber 𝔪 1).card * V)| ≤
        (∑ g, |C g|) * (x ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ α) := by
    rw [show x * Ideal.absNorm 𝔟 * ((dataFiber 𝔪 1).card * V) =
      (dataFiber 𝔪 1).card * (x * Ideal.absNorm 𝔟 * V) by ring]
    exact h.trans (mul_le_mul_of_nonneg_right hCs (by positivity))
  have hκ : (Ideal.absNorm 𝔟 : ℝ) * ((dataFiber 𝔪 1).card * V) /
      (ZLattice.covolume Λ volume * torsionOrder K) = rayDensity 𝔪 := by
    rw [hcov, rayDensity]
    field_simp
  have := abs_sub_le_of_lattice_bound hcov0 htor0 h'
  rwa [hκ] at this

variable (𝔪) in
/-- **Ideals are equidistributed in ray classes**: for every ray class `c`,
`#{𝔞 ∈ c : N𝔞 ≤ x} = κ_𝔪 x + O(x^{1−1/n})` with one density `κ_𝔪` and one constant. -/
theorem exists_abs_ncard_rayClassIdeals_sub_le :
    ∃ C : ℝ, ∀ c : RayClassGroup 𝔪, ∀ x : ℝ, 1 ≤ x →
      |((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x| ≤
        C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  have : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _
  choose C hC using exists_abs_ncard_rayClassIdeals_sub_le_of_class (𝔪 := 𝔪)
  refine ⟨∑ c, |C c|, fun c x hx => (hC c x hx).trans (mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (Finset.single_le_sum (fun c _ => abs_nonneg (C c))
      (Finset.mem_univ c))) (Real.rpow_nonneg (by linarith) _))⟩

/-- The Hecke value of an ideal of norm `≤ x` read off the ray classes. -/
theorem heckeValue_eq_sum_ite [Fintype (RayClassGroup 𝔪)] (ψ : HeckeCharacter 𝔪) {x : ℝ}
    {I : Ideal (𝓞 K)} (hx : (Ideal.absNorm I : ℝ) ≤ x) :
    heckeValue 𝔪 ψ I = ∑ c, if I ∈ rayClassIdeals 𝔪 c x then (ψ c : ℂ) else 0 := by
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    rw [heckeValue_of_mem 𝔪 ψ hI hm, Finset.sum_eq_single (rayClass 𝔪 ⟨_, hm⟩)]
    · rw [if_pos ⟨hI, hm, rfl, hx⟩]
    · intro c _ hc
      rw [if_neg]
      rintro ⟨hI', hm', hc', -⟩
      exact hc hc'.symm
    · simp
  · rw [heckeValue_of_not_mem 𝔪 ψ h]
    refine (Finset.sum_eq_zero fun c _ => if_neg ?_).symm
    rintro ⟨hI', hm', -⟩
    exact h ⟨hI', hm'⟩

/-- **Partial sums of Hecke coefficients split over the ray classes**:
`Σ_{k ≤ x} a_ψ(k) = Σ_c ψ(c) #{𝔞 ∈ c : N𝔞 ≤ x}`. -/
theorem sum_heckeCoeff_eq [Fintype (RayClassGroup 𝔪)] (ψ : HeckeCharacter 𝔪) (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, heckeCoeff 𝔪 ψ k =
      ∑ c, (ψ c : ℂ) * (rayClassIdeals 𝔪 c x).ncard := by
  set A := (Finset.Icc 1 ⌊x⌋₊).biUnion (idealsOfNorm K)
  have hA : ∀ I, I ∈ A ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x := by
    intro I
    simp only [A, Finset.mem_biUnion, Finset.mem_Icc, mem_idealsOfNorm]
    constructor
    · rintro ⟨k, ⟨hk1, hkx⟩, hk⟩
      rw [← hk] at hk1 hkx
      exact ⟨fun h => by simp [h] at hk1, (Nat.le_floor_iff' (by omega)).mp hkx⟩
    · rintro ⟨hI, hx⟩
      have hN : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
      exact ⟨_, ⟨Nat.one_le_iff_ne_zero.mpr hN, (Nat.le_floor_iff' hN).mpr hx⟩, rfl⟩
  have hdisj : ((Finset.Icc 1 ⌊x⌋₊ : Finset ℕ) : Set ℕ).PairwiseDisjoint (idealsOfNorm K) := by
    intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun I hk hl => hkl ?_
    rw [mem_idealsOfNorm] at hk hl
    rw [← hk, ← hl]
  simp only [heckeCoeff]
  rw [← Finset.sum_biUnion hdisj]
  rw [Finset.sum_congr rfl fun I hI => heckeValue_eq_sum_ite ψ ((hA I).mp hI).2,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  rw [← ncard_coe_finset]
  congr 1
  ext I
  simp only [Finset.coe_filter, mem_setOf_eq, and_iff_right_iff_imp]
  rintro ⟨hI, -, -, hx⟩
  exact (hA I).mpr ⟨hI, hx⟩

/-- **Hecke character sums are small**: for `ψ ≠ 1`,
`|Σ_{k ≤ x} a_ψ(k)| = |Σ_{N𝔞 ≤ x} ψ(𝔞)| ≤ C x^{1−1/n}` for `x ≥ 1`. -/
theorem exists_norm_sum_heckeCoeff_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ k ∈ Finset.Icc 1 ⌊x⌋₊, heckeCoeff 𝔪 ψ k‖ ≤ C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  have : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _
  obtain ⟨C, hC⟩ := exists_abs_ncard_rayClassIdeals_sub_le 𝔪
  -- `Σ_c ψ(c) = 0`
  have hψ0 : ∑ c, ((Units.coeHom ℂ).comp ψ) c = 0 := by
    refine sum_hom_units_eq_zero _ fun h => hψ ?_
    ext c
    exact congrArg (· c) h
  refine ⟨Fintype.card (RayClassGroup 𝔪) * C, fun x hx => ?_⟩
  rw [sum_heckeCoeff_eq]
  have hsplit : ∑ c, (ψ c : ℂ) * (rayClassIdeals 𝔪 c x).ncard =
      ∑ c, (ψ c : ℂ) * (((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x : ℝ) := by
    have h0 : ∑ c, (ψ c : ℂ) * ((rayDensity 𝔪 * x : ℝ) : ℂ) = 0 := by
      rw [← Finset.sum_mul]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply] at hψ0
      rw [hψ0, zero_mul]
    rw [← sub_zero (∑ c, (ψ c : ℂ) * (rayClassIdeals 𝔪 c x).ncard), ← h0,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    push_cast
    ring
  rw [hsplit]
  calc ‖∑ c, (ψ c : ℂ) * (((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x : ℝ)‖
      ≤ ∑ c, ‖(ψ c : ℂ) * (((rayClassIdeals 𝔪 c x).ncard : ℝ) - rayDensity 𝔪 * x : ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c : RayClassGroup 𝔪, C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, norm_char_eq_one, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hC c x hx
    _ = Fintype.card (RayClassGroup 𝔪) * C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_assoc]

end GaloisForLFunctions.HeckeLFunctions
