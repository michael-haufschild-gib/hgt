import GaloisForLFunctions.RHTower.WindowRelation

/-!
# The same-point quantum of a reflection configuration

A reflection configuration is a finite effective divisor in `ℂ` closed under line reflection
`s ↦ 1 - conj s` and conjugation, with invariant multiplicities: the four-fold symmetry of the zero
divisor of a completed L-function. Its **collision charge**

  `O = ∑_ρ m_ρ (H_ρ - m_ρ)`,   `H_ρ = ∑_{ρ' : Im ρ' = Im ρ} m_ρ'`

counts ordered pairs of distinct points on a common horizontal line. It is the same-point quantity
behind the horizontal-collision endpoint of `RHTower`, here in the generality of all configurations:

* `O` is even;
* `O = 0` exactly on critical configurations, and `O ≥ 2` otherwise, so criticality is `O < 2`;
* the off-line mass is at most `O`: `N - N₀ ≤ O` (census inequality).

The quantum `2` comes from line reflection: an off-line point and its reflection share an ordinate.
-/

open Complex Finset

namespace GaloisForLFunctions.HilbertianExplicitFormulas

open RHTower (lineReflect lineReflect_re lineReflect_involutive)

/-- A finite effective divisor with the symmetries of a completed L-function divisor. -/
structure ReflectionConfiguration where
  support : Finset ℂ
  mult : ℂ → ℕ
  mult_pos : ∀ ρ ∈ support, 0 < mult ρ
  reflect_mem : ∀ ρ ∈ support, lineReflect ρ ∈ support
  mult_reflect : ∀ ρ, mult (lineReflect ρ) = mult ρ
  conj_mem : ∀ ρ ∈ support, (starRingEnd ℂ) ρ ∈ support
  mult_conj : ∀ ρ, mult ((starRingEnd ℂ) ρ) = mult ρ

namespace ReflectionConfiguration

noncomputable section

variable (Z : ReflectionConfiguration)

theorem lineReflect_im (z : ℂ) : (lineReflect z).im = z.im := by
  simp [lineReflect]

theorem lineReflect_ne_self {ρ : ℂ} (h : ρ.re ≠ 1 / 2) : lineReflect ρ ≠ ρ := by
  intro heq
  have := congrArg Complex.re heq
  rw [lineReflect_re] at this
  exact h (by linarith)

/-- Every point lies on the critical line. -/
def IsCritical : Prop := ∀ ρ ∈ Z.support, ρ.re = 1 / 2

/-- Total multiplicity `N`. -/
def total : ℕ := ∑ ρ ∈ Z.support, Z.mult ρ

/-- Multiplicity on the critical line `N₀`. -/
def lineMass : ℕ := ∑ ρ ∈ Z.support with ρ.re = 1 / 2, Z.mult ρ

/-- Multiplicity off the critical line. -/
def offLineMass : ℕ := ∑ ρ ∈ Z.support with ρ.re ≠ 1 / 2, Z.mult ρ

/-- Horizontal multiplicity `H_ρ`: total multiplicity on the horizontal line through `ρ`. -/
def horizontalMult (ρ : ℂ) : ℕ := ∑ ρ' ∈ Z.support with ρ'.im = ρ.im, Z.mult ρ'

/-- Multiplicity of the other points on the horizontal line through `ρ`. -/
def partnerMult (ρ : ℂ) : ℕ :=
  ∑ ρ' ∈ Z.support with ρ'.im = ρ.im ∧ ρ' ≠ ρ, Z.mult ρ'

/-- The collision charge `O = ∑ m_ρ (H_ρ - m_ρ)`, written with partner multiplicities. -/
def collisionCharge : ℕ := ∑ ρ ∈ Z.support, Z.mult ρ * Z.partnerMult ρ

theorem horizontalMult_eq {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    Z.horizontalMult ρ = Z.mult ρ + Z.partnerMult ρ := by
  rw [horizontalMult, partnerMult,
    ← Finset.sum_filter_add_sum_filter_not (Z.support.filter fun ρ' => ρ'.im = ρ.im)
      (fun ρ' => ρ' = ρ)]
  congr 1
  · rw [Finset.filter_filter]
    have : (Z.support.filter fun ρ' => ρ'.im = ρ.im ∧ ρ' = ρ) = {ρ} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, rfl⟩; rfl
      · rintro rfl; exact ⟨hρ, rfl, rfl⟩
    rw [this, Finset.sum_singleton]
  · rw [Finset.filter_filter]

theorem collisionCharge_eq :
    Z.collisionCharge = ∑ ρ ∈ Z.support, Z.mult ρ * (Z.horizontalMult ρ - Z.mult ρ) := by
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Z.horizontalMult_eq hρ, Nat.add_sub_cancel_left]

/-- An off-line point has its line reflection as a horizontal partner. -/
theorem mult_le_partnerMult_of_offLine {ρ : ℂ} (hρ : ρ ∈ Z.support) (hoff : ρ.re ≠ 1 / 2) :
    Z.mult ρ ≤ Z.partnerMult ρ := by
  rw [← Z.mult_reflect ρ, partnerMult]
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  exact Finset.mem_filter.mpr ⟨Z.reflect_mem ρ hρ, lineReflect_im ρ, lineReflect_ne_self hoff⟩

/-- On the critical line two distinct points never share an ordinate. -/
theorem partnerMult_eq_zero_of_isCritical (hZ : Z.IsCritical) {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    Z.partnerMult ρ = 0 := by
  rw [partnerMult, Finset.sum_eq_zero]
  intro ρ' hρ'
  obtain ⟨hρ'S, him, hne⟩ := Finset.mem_filter.mp hρ'
  exact absurd (Complex.ext (by rw [hZ ρ' hρ'S, hZ ρ hρ]) him) hne

theorem collisionCharge_eq_zero_of_isCritical (hZ : Z.IsCritical) : Z.collisionCharge = 0 :=
  Finset.sum_eq_zero fun ρ hρ => by rw [Z.partnerMult_eq_zero_of_isCritical hZ hρ, mul_zero]

/-- **Quantum.** A configuration with an off-line point has collision charge at least `2`: the point
and its line reflection each see the other. -/
theorem two_le_collisionCharge_of_not_isCritical (hZ : ¬ Z.IsCritical) :
    2 ≤ Z.collisionCharge := by
  simp only [IsCritical, not_forall] at hZ
  obtain ⟨ρ, hρ, hoff⟩ := hZ
  have hρ' : lineReflect ρ ∈ Z.support := Z.reflect_mem ρ hρ
  have hoff' : (lineReflect ρ).re ≠ 1 / 2 := by
    rw [lineReflect_re]; intro h; exact hoff (by linarith)
  have hne : lineReflect ρ ≠ ρ := lineReflect_ne_self hoff
  have hterm : ∀ σ ∈ Z.support, σ.re ≠ 1 / 2 → 1 ≤ Z.mult σ * Z.partnerMult σ := fun σ hσ hσo =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Z.mult_pos σ hσ).ne'
      (Nat.pos_iff_ne_zero.mp ((Z.mult_pos σ hσ).trans_le
        (Z.mult_le_partnerMult_of_offLine hσ hσo))))
  calc 2 = ∑ σ ∈ ({ρ, lineReflect ρ} : Finset ℂ), 1 := by
        rw [Finset.sum_pair hne.symm]
    _ ≤ ∑ σ ∈ ({ρ, lineReflect ρ} : Finset ℂ), Z.mult σ * Z.partnerMult σ := by
        apply Finset.sum_le_sum
        intro σ hσ
        rcases Finset.mem_insert.mp hσ with rfl | hσ
        · exact hterm σ hρ hoff
        · rw [Finset.mem_singleton.mp hσ]; exact hterm _ hρ' hoff'
    _ ≤ Z.collisionCharge := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro σ hσ
          rcases Finset.mem_insert.mp hσ with rfl | hσ
          · exact hρ
          · rw [Finset.mem_singleton.mp hσ]; exact hρ'
        · intro _ _ _; exact Nat.zero_le _

/-- **The quantum law.** Criticality, zero charge and charge below the quantum `2` coincide. -/
theorem isCritical_tfae :
    List.TFAE [Z.IsCritical, Z.collisionCharge = 0, Z.collisionCharge < 2] := by
  tfae_have 1 → 2 := Z.collisionCharge_eq_zero_of_isCritical
  tfae_have 2 → 3 := fun h => by omega
  tfae_have 3 → 1 := fun h => by
    by_contra hZ
    exact absurd (Z.two_le_collisionCharge_of_not_isCritical hZ) (by omega)
  tfae_finish

/-- The collision charge is symmetric in its pairs, hence even: `∑ m H - ∑ m²` with
`∑ m H = ∑_lines H²` and `x² ≡ x (mod 2)`. -/
theorem even_collisionCharge : Even Z.collisionCharge := by
  classical
  -- Sum of `m_ρ * m_ρ'` over ordered pairs of distinct points on a common horizontal line.
  set P := (Z.support ×ˢ Z.support).filter fun p : ℂ × ℂ => p.1.im = p.2.im ∧ p.2 ≠ p.1
  have hP : Z.collisionCharge = ∑ p ∈ P, Z.mult p.1 * Z.mult p.2 := by
    rw [collisionCharge, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [partnerMult, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ' _
    by_cases h : ρ'.im = ρ.im ∧ ρ' ≠ ρ
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩)]
  -- The swap is a fixed-point-free involution of `P` preserving the summand, so mod 2 the sum
  -- cancels in pairs.
  rw [hP, ← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p hp _ => ?_)
    (fun p hp => ?_) (fun p _ => Prod.swap_swap p)
  · rw [Prod.fst_swap, Prod.snd_swap, Nat.mul_comm, ← two_mul]
    exact mul_eq_zero_of_left (by decide) _
  · obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hp
    intro hfix
    exact hne (congrArg Prod.fst hfix)
  · obtain ⟨hpS, him, hne⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hpS).2, (Finset.mem_product.mp hpS).1⟩, him.symm, hne.symm⟩

/-- **Census inequality.** The off-line multiplicity is at most the collision charge. -/
theorem offLineMass_le_collisionCharge : Z.offLineMass ≤ Z.collisionCharge := by
  calc Z.offLineMass = ∑ ρ ∈ Z.support with ρ.re ≠ 1 / 2, Z.mult ρ := rfl
    _ ≤ ∑ ρ ∈ Z.support with ρ.re ≠ 1 / 2, Z.mult ρ * Z.partnerMult ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        obtain ⟨hρS, hoff⟩ := Finset.mem_filter.mp hρ
        exact Nat.le_mul_of_pos_right _ ((Z.mult_pos ρ hρS).trans_le
          (Z.mult_le_partnerMult_of_offLine hρS hoff))
    _ ≤ Z.collisionCharge :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)

theorem total_eq_lineMass_add_offLineMass : Z.total = Z.lineMass + Z.offLineMass :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- `N ≤ N₀ + O`: the census reads the collision charge. -/
theorem total_le_lineMass_add_collisionCharge : Z.total ≤ Z.lineMass + Z.collisionCharge := by
  rw [Z.total_eq_lineMass_add_offLineMass]
  exact Nat.add_le_add_left Z.offLineMass_le_collisionCharge _

/-- **Census constant.** A normalized bound `O ≤ c N` gives the critical proportion `1 - c`. -/
theorem one_sub_mul_total_le_lineMass {c : ℝ} (hO : (Z.collisionCharge : ℝ) ≤ c * Z.total) :
    (1 - c) * Z.total ≤ Z.lineMass := by
  have h := Z.total_le_lineMass_add_collisionCharge
  have h' : (Z.total : ℝ) ≤ Z.lineMass + Z.collisionCharge := by exact_mod_cast h
  nlinarith

end

end ReflectionConfiguration

end GaloisForLFunctions.HilbertianExplicitFormulas
