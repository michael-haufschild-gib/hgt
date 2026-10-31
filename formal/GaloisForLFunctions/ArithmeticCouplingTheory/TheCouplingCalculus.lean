import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex

/-!
# The coupling calculus

For a kernel `K : G → ℂ` on a commutative group the **coupling** of `u` and `v` is the mixed second
difference

  `C_K(u, v) = K(uv) − K(u) − K(v) + K(1)`.

It is the part of `K` that a separable (axial) description cannot see.

* **Künneth splitting** (`sum_mul_coupling_eq`, `coupling_eq_zero_iff_annihilates`): pairing `K`
  against `c ⊗ d` with `Σ c = Σ d = 0` (the mixed augmentation ideal `I₁ ⊗ I₂`) sees only `C_K`, and
  `K` is coupling-free on `A × B` iff every such pairing vanishes.
* **Separability** (`coupling_eq_zero_iff_separable`): coupling-free on `A × B` iff
  `K(uv) = k₁(u) + k₂(v)` there.
* **Characters** (`coupling_monoidHom`): the coupling of a character is `(χ(u) − 1)(χ(v) − 1)`.
* **Polarization** (`coupling_correlation`): for a correlation `K(g) = B(f, T_g f)` of an isometric
  action, `C_K(u, v) = B(T_{u⁻¹}f − f, T_v f − f)`: the coupling is the pairing of difference vectors.
* **Antidiagonal** (`coupling_inv_of_isHermKernel`): for Hermitian `K`,
  `C_K(u, u⁻¹) = 2(K(1) − Re K(u))`: the self-coupling of a scale is the kernel.
* **Coupling Laplacian** (`lap`, `lap_lap_one`, `lap_lap_eq_zero_of_coupling_eq_zero`,
  `negIndex_lap_le`): `L_a K(g) = 2K(g) − K(ga) − K(ga⁻¹)`; `L_a L_b K(1)` is the sum of the four
  couplings `C_K(a^±, b^±)`, `L_a L_b` annihilates every kernel that is coupling-free across two
  subgroups, and differencing never raises the negative index.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

variable {G : Type*} [CommGroup G]

/-! ### The coupling -/

/-- The **coupling** of a kernel: the mixed second difference `K(uv) − K(u) − K(v) + K(1)`. -/
def coupling (K : G → ℂ) (u v : G) : ℂ := K (u * v) - K u - K v + K 1

theorem coupling_comm (K : G → ℂ) (u v : G) : coupling K u v = coupling K v u := by
  simp only [coupling, mul_comm u v]; ring

@[simp] theorem coupling_one_left (K : G → ℂ) (v : G) : coupling K 1 v = 0 := by
  simp [coupling]

@[simp] theorem coupling_one_right (K : G → ℂ) (u : G) : coupling K u 1 = 0 := by
  simp [coupling]

theorem coupling_add (K L : G → ℂ) (u v : G) :
    coupling (fun g => K g + L g) u v = coupling K u v + coupling L u v := by
  simp only [coupling]; ring

theorem coupling_sub (K L : G → ℂ) (u v : G) :
    coupling (fun g => K g - L g) u v = coupling K u v - coupling L u v := by
  simp only [coupling]; ring

theorem coupling_smul (c : ℂ) (K : G → ℂ) (u v : G) :
    coupling (fun g => c * K g) u v = c * coupling K u v := by
  simp only [coupling]; ring

@[simp] theorem coupling_const (c : ℂ) (u v : G) : coupling (fun _ : G => c) u v = 0 := by
  simp [coupling]

/-- The coupling of a finite sum of kernels is the sum of their couplings. -/
theorem coupling_sum {ι : Type*} (s : Finset ι) (K : ι → G → ℂ) (u v : G) :
    coupling (fun g => ∑ i ∈ s, K i g) u v = ∑ i ∈ s, coupling (K i) u v := by
  simp only [coupling, sum_add_distrib, sum_sub_distrib]

/-- **The coupling of a character is a product.** -/
theorem coupling_monoidHom (χ : G →* ℂ) (u v : G) :
    coupling χ u v = (χ u - 1) * (χ v - 1) := by
  simp only [coupling, map_mul, map_one]; ring

/-- The coupling of the translated kernel `x ↦ K(gx)`. -/
theorem coupling_translate (K : G → ℂ) (g u v : G) :
    coupling (fun x => K (g * x)) u v = K (g * u * v) - K (g * u) - K (g * v) + K g := by
  simp only [coupling, mul_assoc, mul_one]

/-! ### Künneth splitting: the mixed augmentation ideal sees only the coupling -/

/-- **Künneth splitting.** Against coefficient families of total mass zero on both factors, a kernel
pairs only through its coupling. -/
theorem sum_mul_coupling_eq {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → G) (y : κ → G)
    (c : ι → ℂ) (d : κ → ℂ) (hc : ∑ i ∈ s, c i = 0) (hd : ∑ j ∈ t, d j = 0) (K : G → ℂ) :
    ∑ i ∈ s, ∑ j ∈ t, c i * d j * coupling K (x i) (y j) =
      ∑ i ∈ s, ∑ j ∈ t, c i * d j * K (x i * y j) := by
  have hexp : ∀ i j, c i * d j * coupling K (x i) (y j) =
      c i * d j * K (x i * y j) - c i * K (x i) * d j - c i * (d j * K (y j)) +
        K 1 * c i * d j := fun i j => by simp only [coupling]; ring
  have hA : ∑ i ∈ s, ∑ j ∈ t, c i * K (x i) * d j = 0 := by
    simp_rw [← mul_sum, hd, mul_zero, sum_const_zero]
  have hB : ∑ i ∈ s, ∑ j ∈ t, c i * (d j * K (y j)) = 0 := by
    simp_rw [← mul_sum, ← sum_mul, hc, zero_mul]
  have hC : ∑ i ∈ s, ∑ j ∈ t, K 1 * c i * d j = 0 := by
    simp_rw [← mul_sum, hd, mul_zero, sum_const_zero]
  simp_rw [hexp, sum_add_distrib, sum_sub_distrib, hA, hB, hC]
  ring

/-- **Coupling-freeness is annihilation by the mixed augmentation ideal.** -/
theorem coupling_eq_zero_iff_annihilates (K : G → ℂ) (A B : Set G) :
    (∀ u ∈ A, ∀ v ∈ B, coupling K u v = 0) ↔
      ∀ (n m : ℕ) (x : Fin n → G) (y : Fin m → G) (c : Fin n → ℂ) (d : Fin m → ℂ),
        (∀ i, x i ∈ A ∨ x i = 1) → (∀ j, y j ∈ B ∨ y j = 1) →
        ∑ i, c i = 0 → ∑ j, d j = 0 → ∑ i, ∑ j, c i * d j * K (x i * y j) = 0 := by
  constructor
  · intro h n m x y c d hx hy hc hd
    rw [← sum_mul_coupling_eq _ _ x y c d hc hd K]
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
    rcases hx i with hxi | hxi
    · rcases hy j with hyj | hyj
      · rw [h _ hxi _ hyj, mul_zero]
      · rw [hyj, coupling_one_right, mul_zero]
    · rw [hxi, coupling_one_left, mul_zero]
  · intro h u hu v hv
    have := h 2 2 ![u, 1] ![v, 1] ![1, -1] ![1, -1]
      (fun i => by fin_cases i <;> simp [hu]) (fun j => by fin_cases j <;> simp [hv])
      (by simp) (by simp)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      mul_one, neg_mul, mul_neg, neg_neg] at this
    rw [coupling]
    linear_combination this

/-- **Coupling-freeness is separability.** -/
theorem coupling_eq_zero_iff_separable (K : G → ℂ) (A B : Set G) (hA : (1 : G) ∈ A)
    (hB : (1 : G) ∈ B) :
    (∀ u ∈ A, ∀ v ∈ B, coupling K u v = 0) ↔
      ∃ k₁ k₂ : G → ℂ, ∀ u ∈ A, ∀ v ∈ B, K (u * v) = k₁ u + k₂ v := by
  constructor
  · intro h
    refine ⟨K, fun v => K v - K 1, fun u hu v hv => ?_⟩
    have := h u hu v hv
    rw [coupling] at this
    linear_combination this
  · rintro ⟨k₁, k₂, hk⟩ u hu v hv
    have h1 := hk u hu v hv
    have h2 := hk u hu 1 hB
    have h3 := hk 1 hA v hv
    have h4 := hk 1 hA 1 hB
    simp only [mul_one, one_mul] at h2 h3 h4
    rw [coupling, h1, h2, h3, h4]
    ring

/-! ### Polarization: the coupling of a correlation -/

/-- **Polarization.** For a correlation `K(g) = B(f, T_g f)` of a `B`-isometric action, the coupling
is the pairing of the difference vectors `T_{u⁻¹}f − f` and `T_v f − f`. -/
theorem coupling_correlation {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (T : G →* Module.End ℂ V)
    (hT : ∀ g x y, B (T g x) (T g y) = B x y) (f : V) (u v : G) :
    coupling (fun g => B f (T g f)) u v = B (T u⁻¹ f - f) (T v f - f) := by
  have h1 : B (T u⁻¹ f) (T v f) = B f (T (u * v) f) := by
    rw [← hT u, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, map_mul, Module.End.mul_apply]
  have h2 : B (T u⁻¹ f) f = B f (T u f) := by
    rw [← hT u, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  have h3 : B f (T 1 f) = B f f := by rw [map_one, Module.End.one_apply]
  simp only [coupling, map_sub, LinearMap.sub_apply, h1, h2, h3]
  ring

/-! ### The antidiagonal -/

theorem isHermKernel_one_eq_re {K : G → ℂ} (hK : IsHermKernel K) : K 1 = ((K 1).re : ℂ) := by
  have h := hK 1
  rw [inv_one] at h
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

/-- **The antidiagonal identity.** For a Hermitian kernel, the coupling of `u` with `u⁻¹` is
`2(K(1) − Re K(u))`. -/
theorem coupling_inv_of_isHermKernel {K : G → ℂ} (hK : IsHermKernel K) (u : G) :
    coupling K u u⁻¹ = ((2 * ((K 1).re - (K u).re) : ℝ) : ℂ) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, K 1 = r := ⟨_, isHermKernel_one_eq_re hK⟩
  rw [coupling, mul_inv_cancel, hK u, hr]
  apply Complex.ext
  · simp; ring
  · simp

/-! ### The coupling Laplacian -/

/-- The second difference `L_a K(g) = 2K(g) − K(ga) − K(ga⁻¹)`. -/
def lap (a : G) (K : G → ℂ) (g : G) : ℂ := 2 * K g - K (g * a) - K (g * a⁻¹)

/-- `L_a L_b K(g)` written out over the nine points `g a^{0,±1} b^{0,±1}`. -/
theorem lap_lap_apply (a b : G) (K : G → ℂ) (g : G) :
    lap a (lap b K) g = 4 * K g - 2 * K (g * a) - 2 * K (g * a⁻¹) - 2 * K (g * b) -
      2 * K (g * b⁻¹) + K (g * a * b) + K (g * a * b⁻¹) + K (g * a⁻¹ * b) +
        K (g * a⁻¹ * b⁻¹) := by
  simp only [lap]; ring

/-- **The coupling Laplacian at the identity is the sum of the four couplings `C_K(a^±, b^±)`.** -/
theorem lap_lap_one (a b : G) (K : G → ℂ) :
    lap a (lap b K) 1 = coupling K a b + coupling K a⁻¹ b + coupling K a b⁻¹ +
      coupling K a⁻¹ b⁻¹ := by
  rw [lap_lap_apply]
  simp only [coupling, one_mul]
  ring

/-- **The coupling Laplacian annihilates coupling-free kernels.** If `K` has zero coupling across
the subgroups `H₁, H₂`, then `L_a L_b K` vanishes on `H₁H₂` for `a ∈ H₁`, `b ∈ H₂`. -/
theorem lap_lap_eq_zero_of_coupling_eq_zero {K : G → ℂ} {H₁ H₂ : Subgroup G}
    (h : ∀ u ∈ H₁, ∀ v ∈ H₂, coupling K u v = 0) {a b : G} (ha : a ∈ H₁) (hb : b ∈ H₂)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ H₁) (hg₂ : g₂ ∈ H₂) : lap a (lap b K) (g₁ * g₂) = 0 := by
  obtain ⟨k₁, k₂, hk⟩ := (coupling_eq_zero_iff_separable K H₁ H₂ H₁.one_mem H₂.one_mem).mp h
  have e : ∀ x y : G, g₁ * g₂ * x * y = (g₁ * x) * (g₂ * y) := fun x y => by
    simp only [mul_assoc, mul_left_comm g₂ x]
  have e1 : ∀ x : G, g₁ * g₂ * x = (g₁ * x) * (g₂ * 1) := fun x => by
    rw [mul_one, mul_right_comm]
  have e2 : ∀ y : G, g₁ * g₂ * y = (g₁ * 1) * (g₂ * y) := fun y => by
    rw [mul_one, mul_assoc]
  rw [lap_lap_apply, e, e, e, e, e1 a, e1 a⁻¹, e2 b, e2 b⁻¹,
    hk _ (H₁.mul_mem hg₁ ha) _ (H₂.mul_mem hg₂ hb),
    hk _ (H₁.mul_mem hg₁ ha) _ (H₂.mul_mem hg₂ (H₂.inv_mem hb)),
    hk _ (H₁.mul_mem hg₁ (H₁.inv_mem ha)) _ (H₂.mul_mem hg₂ hb),
    hk _ (H₁.mul_mem hg₁ (H₁.inv_mem ha)) _ (H₂.mul_mem hg₂ (H₂.inv_mem hb)),
    hk _ (H₁.mul_mem hg₁ ha) _ (H₂.mul_mem hg₂ H₂.one_mem),
    hk _ (H₁.mul_mem hg₁ (H₁.inv_mem ha)) _ (H₂.mul_mem hg₂ H₂.one_mem),
    hk _ (H₁.mul_mem hg₁ H₁.one_mem) _ (H₂.mul_mem hg₂ hb),
    hk _ (H₁.mul_mem hg₁ H₁.one_mem) _ (H₂.mul_mem hg₂ (H₂.inv_mem hb)),
    hk _ hg₁ _ hg₂]
  simp only [mul_one]
  ring

theorem isHermKernel_lap {K : G → ℂ} (hK : IsHermKernel K) (a : G) : IsHermKernel (lap a K) :=
  fun g => by
    have h1 : K (g⁻¹ * a) = conj (K (g * a⁻¹)) := by rw [← hK, mul_inv_rev, inv_inv, mul_comm]
    have h2 : K (g⁻¹ * a⁻¹) = conj (K (g * a)) := by rw [← hK, mul_inv_rev, mul_comm]
    simp only [lap, map_sub, map_mul, map_ofNat, h1, h2, hK g]
    ring

/-- The Gram form of `L_a K` on a family is the Gram form of `K` on the doubled family
`x_i, x_i a` with coefficients `c_i, −c_i`. -/
theorem hermQuad_gram_lap {n : ℕ} (a : G) (K : G → ℂ) (x : Fin n → G) (c : Fin n → ℂ) :
    hermQuad (gram (lap a K) x) c =
      hermQuad (gram K (Sum.elim x fun i => x i * a)) (Sum.elim c fun i => -c i) := by
  rw [hermQuad_gram, hermQuad_gram]
  congr 1
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have e1 : (x i * a)⁻¹ * x j = (x i)⁻¹ * x j * a⁻¹ := by
    rw [mul_inv_rev, mul_comm a⁻¹ (x i)⁻¹, mul_assoc, mul_comm a⁻¹ (x j), ← mul_assoc]
  have e2 : (x i)⁻¹ * (x j * a) = (x i)⁻¹ * x j * a := (mul_assoc _ _ _).symm
  have e3 : (x i * a)⁻¹ * (x j * a) = (x i)⁻¹ * x j := by
    rw [mul_inv_rev, mul_comm (x j) a, mul_assoc, ← mul_assoc (x i)⁻¹ a (x j),
      mul_comm (x i)⁻¹ a, mul_assoc a, inv_mul_cancel_left]
  rw [e1, e2, e3, lap]
  ring

/-- **Differencing never raises the negative index**: `κ(L_a K) ≤ κ(K)`. -/
theorem negIndex_lap_le (a : G) (K : G → ℂ) : negIndex (lap a K) ≤ negIndex K := by
  rw [negIndex_le_iff]
  intro n x
  set L : (Fin n → ℂ) →ₗ[ℂ] (Fin n ⊕ Fin n → ℂ) :=
    { toFun := fun c => Sum.elim c fun i => -c i
      map_add' := fun c d => by funext k; cases k <;> simp [add_comm]
      map_smul' := fun t c => by funext k; cases k <;> simp }
  have hle := hermNegIndex_le_of_hermQuad_eq (gram (lap a K) x)
    (gram K (Sum.elim x fun i => x i * a)) L fun c => (hermQuad_gram_lap a K x c).symm
  exact (Nat.cast_le.mpr hle).trans (hermNegIndex_gram_le_negIndex _ _)

/-- **The coupling Laplacian never raises the negative index.** -/
theorem negIndex_lap_lap_le (a b : G) (K : G → ℂ) : negIndex (lap a (lap b K)) ≤ negIndex K :=
  (negIndex_lap_le a _).trans (negIndex_lap_le b K)

end GaloisForLFunctions.ArithmeticCouplingTheory
