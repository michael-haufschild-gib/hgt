import GaloisForLFunctions.HTGeometry.RittSecondJetAffineConnection
import GaloisForLFunctions.HTGeometry.RittLogDerivativeObstruction

/-!
# An eigenvector in the first jet field carries a rational affine connection

Let `x` be a nonzero element of `K⟮τ⟯` with `σ x = c · x` and `c = q^i · ρ^k`.  Its logarithmic
derivative `v = d x / x` lives in the *second* jet field `K⟮τ, d τ⟯`, and the chain rule turns the
eigen-relation into

`ρ · σ(v) = v + k · dK ρ / ρ`.

Two coprime slicings — first in `d τ` over `K⟮τ⟯`, where the shift scales by `q/ρ`, then in `τ` over
`K`, where it scales by `q` — bring that equation down to the base:

`ρ · ψ(a) = a + k · dK ρ / ρ`,

which for `k ≠ 0` is the rational affine-connection equation after scaling by `−k`.

This is the obstruction the fully degenerate branch of the tower descent produces: there every
coefficient of the sliced fraction is a derivation constant, so the surviving element is an
eigenvector of the shift inside the first jet field.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RittFrame

variable (Fr : RittFrame K L)

theorem d_one : Fr.d 1 = 0 := by
  have h := Fr.d_base 1
  rw [map_one, Fr.dK_one, map_zero] at h
  exact h

theorem d_inv {y : L} (hy : y ≠ 0) : Fr.d y⁻¹ = -(Fr.d y) * (y⁻¹ * y⁻¹) := by
  have hprod : Fr.d (y * y⁻¹) = Fr.d 1 := by rw [mul_inv_cancel₀ hy]
  rw [Fr.d_mul, Fr.d_one] at hprod
  have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
  refine mul_left_cancel₀ hy ?_
  calc y * Fr.d y⁻¹ = -(Fr.d y * y⁻¹) := by linear_combination hprod
    _ = y * (-(Fr.d y) * (y⁻¹ * y⁻¹)) := by
        linear_combination (Fr.d y * y⁻¹) * hyy

/-- The derivation carries the first jet field into the second. -/
theorem d_mem_adjoin_two_of_mem_adjoin_one {τ : L} {x : L}
    (hx : x ∈ IntermediateField.adjoin K ({τ} : Set L)) :
    x ∈ IntermediateField.adjoin K ({τ, Fr.d τ} : Set L) ∧
      Fr.d x ∈ IntermediateField.adjoin K ({τ, Fr.d τ} : Set L) := by
  classical
  set E : IntermediateField K L := IntermediateField.adjoin K ({τ, Fr.d τ} : Set L) with hE
  have hzero : Fr.d 0 = 0 := Fr.d_zero
  have hle : IntermediateField.adjoin K ({τ} : Set L) ≤
      { carrier := {y : L | y ∈ E ∧ Fr.d y ∈ E}
        mul_mem' := fun {y z} hy hz => by
          refine ⟨mul_mem hy.1 hz.1, ?_⟩
          rw [Fr.d_mul]
          exact add_mem (mul_mem hy.2 hz.1) (mul_mem hy.1 hz.2)
        one_mem' := ⟨one_mem E, by rw [Fr.d_one]; exact zero_mem E⟩
        add_mem' := fun {y z} hy hz => by
          refine ⟨add_mem hy.1 hz.1, ?_⟩
          rw [Fr.d_add]
          exact add_mem hy.2 hz.2
        zero_mem' := ⟨zero_mem E, by rw [hzero]; exact zero_mem E⟩
        algebraMap_mem' := fun a => by
          refine ⟨IntermediateField.algebraMap_mem E a, ?_⟩
          rw [Fr.d_base]
          exact IntermediateField.algebraMap_mem E _
        inv_mem' := fun y hy => by
          rcases eq_or_ne y 0 with rfl | hy0
          · refine ⟨?_, ?_⟩
            · simp only [inv_zero]
              exact zero_mem E
            · rw [inv_zero, hzero]
              exact zero_mem E
          · refine ⟨inv_mem hy.1, ?_⟩
            rw [Fr.d_inv hy0]
            exact mul_mem (neg_mem hy.2) (mul_mem (inv_mem hy.1) (inv_mem hy.1)) } := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro y hy
    rw [show y = τ by simpa using hy]
    exact ⟨IntermediateField.subset_adjoin K _ (by simp),
      IntermediateField.subset_adjoin K _ (by simp)⟩
  exact hle hx

/-- **The logarithmic form of an eigen-relation in the extension.** -/
theorem dLog_relation_of_eigen_L {x : L} {c : K} (hx : x ≠ 0) (hc : c ≠ 0)
    (h : Fr.σ x = algebraMap K L c * x) :
    algebraMap K L Fr.ρ * Fr.σ (Fr.d x / x)
      = Fr.d x / x + algebraMap K L (Fr.dKLog c) := by
  have hcL : algebraMap K L c ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hc
  have hchain := Fr.chain x
  rw [h, Fr.d_mul, Fr.d_base] at hchain
  have hσx : Fr.σ x ≠ 0 := by
    rw [h]
    exact mul_ne_zero hcL hx
  have hdiv : Fr.σ (Fr.d x / x) = Fr.σ (Fr.d x) / (algebraMap K L c * x) := by
    rw [map_div₀, h]
  rw [hdiv, dKLog, map_div₀]
  field_simp
  linear_combination -hchain

/-- **Two slicings bring an affine relation over the second jet field down to the base.** -/
theorem exists_base_affine_of_secondJetField [CharZero L] {τ : L} {q : K}
    (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (hτtr : Transcendental K τ)
    (hdτtr : Transcendental ↥(IntermediateField.adjoin K ({τ} : Set L)) (Fr.d τ))
    {b : L} (hb : b ∈ IntermediateField.adjoin K ({τ, Fr.d τ} : Set L)) {γ : K}
    (hrel : algebraMap K L Fr.ρ * Fr.σ b = b + algebraMap K L γ) :
    ∃ a : K, Fr.ρ * Fr.ψ a = a + γ := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set E₀ : IntermediateField K L := IntermediateField.adjoin K ({τ} : Set L) with hE₀
  have hτE : τ ∈ E₀ := IntermediateField.subset_adjoin K _ (by simp)
  have hE₀σ : ∀ y ∈ E₀, Fr.σ y ∈ E₀ := by
    refine Fr.sigma_mem_of_mem_adjoin ?_
    intro y hy
    rw [show y = τ by simpa using hy, hshift]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) hτE
  set φ₀ : ↥E₀ →+* ↥E₀ :=
    { toFun := fun y => ⟨Fr.σ (y : L), hE₀σ (y : L) y.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp } with hφ₀
  have hcomp₀ : ∀ y : ↥E₀, Fr.σ (algebraMap ↥E₀ L y) = algebraMap ↥E₀ L (φ₀ y) := fun _ => rfl
  -- the first slicing, in `d τ` over `K⟮τ⟯`
  set μ₀ : ↥E₀ := ⟨algebraMap K L (q / Fr.ρ), IntermediateField.algebraMap_mem _ _⟩ with hμ₀
  have hμ₀0 : μ₀ ≠ 0 := by
    intro h0
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (div_ne_zero hq hρ0))
      (congrArg Subtype.val h0)
  set ν₀ : ↥E₀ := ⟨algebraMap K L Fr.ρ, IntermediateField.algebraMap_mem _ _⟩ with hν₀
  set β₀ : ↥E₀ := ⟨algebraMap K L γ, IntermediateField.algebraMap_mem _ _⟩ with hβ₀
  have hσdτ : Fr.σ (Fr.d τ) = algebraMap ↥E₀ L μ₀ * Fr.d τ :=
    Fr.sigma_d_eq_of_shift hqconst hshift
  have hbmem : b ∈ IntermediateField.adjoin ↥E₀ ({Fr.d τ} : Set L) := by
    have hset : ({τ} : Set L) ∪ ({Fr.d τ} : Set L) = ({τ, Fr.d τ} : Set L) := by
      ext y; simp [or_comm]
    have heq : (IntermediateField.adjoin ↥E₀ ({Fr.d τ} : Set L)).restrictScalars K
        = IntermediateField.adjoin K ({τ, Fr.d τ} : Set L) := by
      rw [hE₀, IntermediateField.adjoin_adjoin_left, hset]
    have hb' : b ∈ (IntermediateField.adjoin ↥E₀ ({Fr.d τ} : Set L)).restrictScalars K := by
      rw [heq]; exact hb
    exact hb'
  have hrel₀ : algebraMap ↥E₀ L ν₀ * Fr.σ b = b + algebraMap ↥E₀ L β₀ := hrel
  obtain ⟨a₁, ha₁⟩ :=
    exists_eigen_shift_solution_of_mem_adjoin Fr.σ φ₀ hcomp₀ hdτtr hμ₀0 hσdτ hbmem hrel₀
  -- the second slicing, in `τ` over the base
  have ha₁L : algebraMap K L Fr.ρ * Fr.σ (a₁ : L) = (a₁ : L) + algebraMap K L γ := by
    have h := congrArg (fun z : ↥E₀ => (z : L)) ha₁
    simp only [hφ₀, hν₀, hβ₀] at h
    push_cast at h
    linear_combination h
  exact exists_eigen_shift_solution_of_mem_adjoin Fr.σ Fr.ψ Fr.comp hτtr (μ := q) (ν := Fr.ρ)
    hq hshift a₁.2 ha₁L

/-- **An eigenvector in the first jet field carries a rational affine connection.** -/
theorem exists_base_affine_of_firstJetField_eigen [CharZero L] {τ : L} {q : K}
    (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (hτtr : Transcendental K τ)
    (hdτtr : Transcendental ↥(IntermediateField.adjoin K ({τ} : Set L)) (Fr.d τ))
    {x : L} (hx0 : x ≠ 0) (hx : x ∈ IntermediateField.adjoin K ({τ} : Set L)) {i k : ℤ}
    (h : Fr.σ x = algebraMap K L (q ^ i * Fr.ρ ^ k) * x) :
    ∃ a : K, Fr.ρ * Fr.ψ a = a + (k : K) * Fr.dKLog Fr.ρ := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hc0 : q ^ i * Fr.ρ ^ k ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq) (zpow_ne_zero _ hρ0)
  have hlog : Fr.dKLog (q ^ i * Fr.ρ ^ k) = (k : K) * Fr.dKLog Fr.ρ := by
    rw [Fr.dKLog_mul (zpow_ne_zero _ hq) (zpow_ne_zero _ hρ0), Fr.dKLog_zpow hq,
      Fr.dKLog_zpow hρ0]
    have hq0 : Fr.dKLog q = 0 := by rw [dKLog, hqconst, zero_div]
    rw [hq0, mul_zero, zero_add]
  obtain ⟨hxmem, hdxmem⟩ := Fr.d_mem_adjoin_two_of_mem_adjoin_one hx
  have hb : Fr.d x / x ∈ IntermediateField.adjoin K ({τ, Fr.d τ} : Set L) :=
    div_mem hdxmem hxmem
  have hrel := Fr.dLog_relation_of_eigen_L hx0 hc0 h
  rw [hlog] at hrel
  exact Fr.exists_base_affine_of_secondJetField hq hqconst hshift hτtr hdτtr hb hrel

end RittFrame

end GaloisForLFunctions.HTGeometry
