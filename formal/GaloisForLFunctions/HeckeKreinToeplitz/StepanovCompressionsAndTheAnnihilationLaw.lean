import GaloisForLFunctions.HeckeKreinToeplitz.LogarithmicCharactersAndTheArithmeticIndexFormula

/-!
# Stepanov compressions and the annihilation law

An auxiliary construction in the sense of Stepanov is a finitely supported **compressor**
`P = Σ_α p_α δ_{y_α}` on the group. It compresses a kernel to
`k_P(u) = Σ_{α,β} p̄_α p_β k(y_α⁻¹ u y_β)` (`compress`): the Toeplitz form of `k_P` on a family `x_i`
with coefficients `c_i` is the form of `k` on the family `x_i y_α` with coefficients `c_i p_α`
(`hermQuad_gram_compress`). Compression never raises the index (`negIndex_compress_le`) and keeps
positive definiteness (`IsPosDefKernel.compress`).

**Compression of a pair** (`compress_pairKernel`). With the transform `P̂(χ) = Σ_α p_α χ(y_α)`,
the compression of `h_{χ,ω}` is the pair `h_{χ, ω P̂(χ) conj P̂(χ†)}`: the weight is multiplied by the
values of `P̂` at both characters of the pair.

**The annihilation law** (`negIndex_compress_eq`). For a Krein–Langer kernel separated at one
element, the index of its compression is the number of pairs at neither of whose characters `P̂`
vanishes. A compression is positive definite iff `P̂` vanishes at one character of every pair
(`isPosDefKernel_compress_iff`).

**Arithmetic reading** (`hat_zeroChar`). On `ℚ_{>0}` the transform at `u ↦ u^{ρ−1/2}` is the Dirichlet
polynomial `D_P(s) = Σ_α p_α y_α^s` at `s = ρ − ½`, and at the reflected character at `s = ½ − ρ̄`. A
Stepanov certificate for the Weil kernel is a Dirichlet polynomial vanishing at `ρ − ½` or at `½ − ρ̄`
for every zero right of the line; it must vanish off the critical line, where the Frobenius lattice
of a curve has no analogue.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {β : Type*} [Fintype β]

/-- The compression `k_P(u) = Σ_{α,β} p̄_α p_β k(y_α⁻¹ u y_β)` of a kernel by `P = Σ_α p_α δ_{y_α}`. -/
def compress (k : G → ℂ) (y : β → G) (p : β → ℂ) (u : G) : ℂ :=
  ∑ a, ∑ b, conj (p a) * p b * k ((y a)⁻¹ * u * y b)

/-- The transform `P̂(χ) = Σ_α p_α χ(y_α)` of a compressor. -/
def hat (y : β → G) (p : β → ℂ) (χ : G →* ℂ) : ℂ := ∑ a, p a * χ (y a)

/-- **The compressed form is the form on the product family.** -/
theorem hermQuad_gram_compress (k : G → ℂ) (y : β → G) (p : β → ℂ) {ι : Type*} [Fintype ι]
    (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (compress k y p) x) c =
      hermQuad (gram k fun ia : ι × β => x ia.1 * y ia.2) fun ia => c ia.1 * p ia.2 := by
  rw [hermQuad_gram, hermQuad_gram, Fintype.sum_prod_type]
  congr 1
  simp only [compress, mul_sum, sum_mul, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun j _ => sum_congr rfl fun b _ => ?_
  rw [map_mul, show (x i * y a)⁻¹ * (x j * y b) = (y a)⁻¹ * ((x i)⁻¹ * x j) * y b by group]
  ring

/-- **Compression never raises the index.** -/
theorem negIndex_compress_le (k : G → ℂ) (y : β → G) (p : β → ℂ) :
    negIndex (compress k y p) ≤ negIndex k := by
  rw [negIndex_le_iff]
  intro n x
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin n × β → ℂ) :=
    { toFun := fun c ia => c ia.1 * p ia.2
      map_add' := fun c d => funext fun ia => by simp [add_mul]
      map_smul' := fun t c => funext fun ia => by simp [mul_assoc] }
  exact (Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _ L fun c =>
    (hermQuad_gram_compress k y p x c).symm)).trans (hermNegIndex_gram_le_negIndex k _)

theorem IsHermKernel.compress {k : G → ℂ} (hk : IsHermKernel k) (y : β → G) (p : β → ℂ) :
    IsHermKernel (compress k y p) := fun u => by
  simp only [HeckeKreinToeplitz.compress, map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [show (y b)⁻¹ * u⁻¹ * y a = ((y a)⁻¹ * u * y b)⁻¹ by group, hk]
  ring

/-- Compression keeps positive definiteness. -/
theorem IsPosDefKernel.compress {k : G → ℂ} (hk : IsPosDefKernel k) (y : β → G) (p : β → ℂ) :
    IsPosDefKernel (compress k y p) :=
  (isPosDefKernel_iff (hk.1.compress y p)).mpr
    (nonpos_iff_eq_zero.mp ((negIndex_compress_le k y p).trans hk.negIndex_eq_zero.le))

theorem compress_add (k₁ k₂ : G → ℂ) (y : β → G) (p : β → ℂ) :
    compress (fun u => k₁ u + k₂ u) y p = fun u => compress k₁ y p u + compress k₂ y p u := by
  funext u
  simp only [compress, mul_add, sum_add_distrib]

theorem compress_sum {J : Type*} (s : Finset J) (k : J → G → ℂ) (y : β → G) (p : β → ℂ) :
    compress (fun u => ∑ j ∈ s, k j u) y p = fun u => ∑ j ∈ s, compress (k j) y p u := by
  classical
  induction s using Finset.induction_on with
  | empty => funext u; simp [compress]
  | insert i s hi ih =>
    simp_rw [sum_insert hi]
    rw [compress_add, ih]

/-- **Compression of a pair**: the weight is multiplied by the transform at both characters. -/
theorem compress_pairKernel (χ : G →* ℂ) (ω : ℂ) (y : β → G) (p : β → ℂ) :
    compress (pairKernel χ ω) y p =
      pairKernel χ (ω * hat y p χ * conj (hat y p (reflectChar χ))) := by
  funext u
  have h1 : ∑ a, conj (p a) * χ (y a)⁻¹ = conj (hat y p (reflectChar χ)) := by
    simp only [hat, map_sum, map_mul, conj_reflectChar]
  have h2 : ∑ a, conj (p a) * reflectChar χ (y a)⁻¹ = conj (hat y p χ) := by
    simp only [hat, map_sum, map_mul, reflectChar_inv]
  have key : ∀ a b, conj (p a) * p b * pairKernel χ ω ((y a)⁻¹ * u * y b) =
      ω * χ u * (conj (p a) * χ (y a)⁻¹ * (p b * χ (y b))) +
        conj ω * reflectChar χ u *
          (conj (p a) * reflectChar χ (y a)⁻¹ * (p b * reflectChar χ (y b))) := fun a b => by
    simp only [pairKernel, map_mul]
    ring
  rw [compress, sum_congr rfl fun a _ => sum_congr rfl fun b _ => key a b]
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul]
  rw [h1, h2]
  simp only [pairKernel, hat, map_mul, conj_conj]
  ring

variable {κ : ℕ}

/-- **The annihilation law.** For a positive-definite kernel plus `κ` pairs separated at `u`, the
compression has as many negative squares as pairs not annihilated at either character. -/
theorem negIndex_compress_eq {p₀ : G → ℂ} (hp : IsPosDefKernel p₀) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u)) (y : β → G) (p : β → ℂ) :
    negIndex (compress (fun g => p₀ g + ∑ j, pairKernel (χ j) (ω j) g) y p) =
      (univ.filter fun j => hat y p (χ j) ≠ 0 ∧ hat y p (reflectChar (χ j)) ≠ 0).card := by
  classical
  set S := univ.filter fun j => hat y p (χ j) ≠ 0 ∧ hat y p (reflectChar (χ j)) ≠ 0
  set e := S.equivFin
  set ω' : Fin κ → ℂ := fun j => ω j * hat y p (χ j) * conj (hat y p (reflectChar (χ j)))
  have hω' : ∀ j, ω' j ≠ 0 ↔ j ∈ S := fun j => by
    simp only [ω', S, mem_filter, mem_univ, true_and, ne_eq, mul_eq_zero, map_eq_zero, not_or]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hω j, h.1⟩, h.2⟩⟩
  have hk : compress (fun g => p₀ g + ∑ j, pairKernel (χ j) (ω j) g) y p =
      fun g => compress p₀ y p g + ∑ i, pairKernel (χ (e.symm i)) (ω' (e.symm i)) g := by
    rw [compress_add, compress_sum]
    funext g
    simp only [compress_pairKernel]
    congr 1
    rw [(Finset.sum_subset (subset_univ S) fun j _ hj => by
      have h0 : ω' j = 0 := not_not.mp fun h => hj ((hω' j).mp h)
      simp only [ω'] at h0
      simp [pairKernel, h0]).symm, ← S.sum_coe_sort, ← e.symm.sum_comp]
  have hinj : Function.Injective (fun i : Fin S.card => (e.symm i : Fin κ)) :=
    fun i i' h => e.symm.injective (Subtype.ext h)
  have hnodes : nodes (fun i => χ (e.symm i : Fin κ)) u =
      nodes χ u ∘ Sum.map (fun i => (e.symm i : Fin κ)) (fun i => (e.symm i : Fin κ)) := by
    funext m; rcases m with i | i <;> rfl
  rw [hk, negIndex_add_sum_pairKernel_eq (hp.compress y p) _ _ (fun i => (hω' _).mpr (e.symm i).2)
    u (fun i => hne _) (by rw [hnodes]; exact hsep.comp (Sum.map_injective.mpr ⟨hinj, hinj⟩))]

/-- **A compression is positive definite iff it annihilates one character of every pair.** -/
theorem negIndex_compress_eq_zero_iff {p₀ : G → ℂ} (hp : IsPosDefKernel p₀)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u)) (y : β → G) (p : β → ℂ) :
    negIndex (compress (fun g => p₀ g + ∑ j, pairKernel (χ j) (ω j) g) y p) = 0 ↔
      ∀ j, hat y p (χ j) = 0 ∨ hat y p (reflectChar (χ j)) = 0 := by
  rw [negIndex_compress_eq hp χ ω hω u hne hsep y p, Nat.cast_eq_zero, card_eq_zero,
    filter_eq_empty_iff]
  simp only [mem_univ, true_implies, not_and_or, not_not]

/-! ### The arithmetic reading -/

/-- On `ℚ_{>0}` the transform at `u ↦ u^{s}` is the Dirichlet polynomial `Σ_α p_α y_α^{s}`. -/
theorem hat_logChar (y : β → HeckeLattice) (p : β → ℂ) (s : ℂ) :
    hat y p (logChar heckeLogScale s) = ∑ a, p a * cexp (s * Real.log ((y a : ℚ) : ℝ)) := by
  simp only [hat, logChar_apply, scale_heckeLogScale]

/-- The transform at the reflected character of `ρ` is the Dirichlet polynomial at `½ − ρ̄`. -/
theorem hat_reflect_zeroChar (y : β → HeckeLattice) (p : β → ℂ) (ρ : ℂ) :
    hat y p (reflectChar (zeroChar ρ)) = hat y p (logChar heckeLogScale (1 / 2 - conj ρ)) := by
  rw [reflectChar_logChar]
  congr 2
  rw [map_sub, map_div₀, map_one, map_ofNat]
  ring

end GaloisForLFunctions.HeckeKreinToeplitz
