import GaloisForLFunctions.AdelicKreinGeometry.TheWitnessComplementIsPositive
import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectiveIndexOfTheAtomicKernelIsOneSquare
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity

/-!
# The signature of a separable assembly

A signature formula of Hirzebruch type, exact in the model where the local constituents are
decoupled. Let `H_p` (`p ∈ S`, `S` finite) be groups, `k_p` Hermitian kernels on them, and

  `K(g) = Σ_p k_p(g_p)`  on  `G = Π_p H_p`

their **separable assembly**. The constant function is the one direction all local constituents
share: adding a constant to `k_p` moves `K` only along it. Its polar hyperplane is
`{c : Σ_a c_a = 0}`, and the **polar index** `κ₀(k)` counts the negative squares of `k` on it.

* **The signature formula** (`polarIndex_sum_le_negIndex_separable`,
  `negIndex_separable_le_polarIndex_sum_add_one`):

    `Σ_p κ₀(k_p) ≤ κ(K) ≤ Σ_p κ₀(k_p) + 1`.

  The global index is the sum of the local polar indices plus a gluing term of at most one square,
  carried by the shared pole direction.
* *Lower bound.* Embed a polar negative subspace of each `k_p` on its own axis. On mean-zero blocks
  every constant and every term depending on one block only cancels, so different axes are
  `K`-orthogonal and the local negative subspaces add (`hermQuad_gram_axes`).
* *Upper bound.* The Gram matrix of `K` on any family is the sum of the local Gram matrices
  (`gram_separable`). On the polar hyperplane each is nonnegative off the `κ₀(k_p)` functionals
  of a maximal polar negative subspace (`hermQuad_nonneg_of_orth_maximal`); together with the
  total mass these are `1 + Σ_p κ₀(k_p)` conditions (`hermNegIndex_sum_le`).
* **Matched counterterms.** Polar indices ignore constants, so local counterterms change only
  the gluing square.
* **The negative log-height** (`negIndex_negLogHeight`): on `ℤ` the kernel `−|m|` is conditionally
  positive, `κ₀ = 0` (`polarIndex_negAbsKernel`), so `−Σ_p a_p|m_p|` with weights `a ≥ 0`, not all
  zero, has exactly one negative square. With `a_p = log p` this is `−log(nd)` on the `S`-units:
  the logarithm of the Hecke weight is an index-one Pontryagin state glued by the pole alone.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticLorentzianGeometry (hermPair hermPair_swap
  hermQuad_smul_add_of_orth hermPair_add_left hermPair_smul_left)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Negative squares on a subspace -/

section Matrices

variable {ι : Type*} [Fintype ι]

/-- A linear map into `V` on which the form is negative definite gives that many negative squares
inside `V`. -/
theorem card_le_negIndexOn_of_forall_neg {J : Type*} [Fintype J] (H : Matrix ι ι ℂ)
    (V : Submodule ℂ (ι → ℂ)) (L : (J → ℂ) →ₗ[ℂ] (ι → ℂ)) (hV : ∀ a, L a ∈ V)
    (h : ∀ a, a ≠ 0 → hermQuad H (L a) < 0) : Fintype.card J ≤ negIndexOn H V := by
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    by_contra ha0
    have := h a ha0
    rw [LinearMap.mem_ker.mp ha] at this
    simp [hermQuad] at this
  have hpos : IsPosDefOn (-H) (LinearMap.range L) := by
    rintro y ⟨a, rfl⟩ hy
    have ha : a ≠ 0 := by rintro rfl; exact hy (map_zero L)
    rw [hermQuad_neg]
    linarith [h a ha]
  have hle : LinearMap.range L ≤ V := by rintro _ ⟨a, rfl⟩; exact hV a
  have := finrank_le_negIndexOn hle hpos
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at this

/-- A form nonnegative on `V` has no negative square inside `V`. -/
theorem negIndexOn_eq_zero_of_nonneg {H : Matrix ι ι ℂ} {V : Submodule ℂ (ι → ℂ)}
    (h : ∀ c ∈ V, 0 ≤ hermQuad H c) : negIndexOn H V = 0 := by
  obtain ⟨W, hWV, hr, hW⟩ := exists_negIndexOn H V
  rw [← hr]
  by_contra hne
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W)
    (fun hbot => hne (by rw [hbot]; simp))
  have h1 := hW w hw hw0
  rw [hermQuad_neg] at h1
  linarith [h w (hWV hw)]

/-- **The complement of a maximal negative subspace is nonnegative.** Inside `V`, a vector
`H`-orthogonal to a negative subspace of maximal dimension has nonnegative form. -/
theorem hermQuad_nonneg_of_orth_maximal {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {V W : Submodule ℂ (ι → ℂ)} (hWV : W ≤ V) (hW : IsPosDefOn (-H) W)
    (hmax : Module.finrank ℂ W = negIndexOn H V) {c : ι → ℂ} (hc : c ∈ V)
    (horth : ∀ w ∈ W, hermPair H w c = 0) : 0 ≤ hermQuad H c := by
  by_contra hneg
  push Not at hneg
  set r := Module.finrank ℂ W
  set bW := Module.finBasis ℂ W
  let L : (Option (Fin r) → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun β => β none • c + fun a => ∑ i, β (some i) * ((bW i : W) : ι → ℂ) a
      map_add' := fun β β' => by
        funext a
        simp [add_mul, sum_add_distrib]
        ring
      map_smul' := fun t β => by
        funext a
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add,
          Finset.mul_sum]
        congr 1
        · ring
        · exact sum_congr rfl fun i _ => by ring }
  set wv : (Option (Fin r) → ℂ) → W := fun β => ∑ i, β (some i) • bW i
  have hwv : ∀ β, ((wv β : W) : ι → ℂ) = fun a => ∑ i, β (some i) * ((bW i : W) : ι → ℂ) a :=
    fun β => by funext a; simp [wv, Finset.sum_apply]
  have hL : ∀ β, L β = β none • c + ((wv β : W) : ι → ℂ) := fun β => by rw [hwv]; rfl
  have hneg' : ∀ β, β ≠ 0 → hermQuad H (L β) < 0 := by
    intro β hβ
    have horth' : hermPair H c (wv β) = 0 := by
      rw [hermPair_swap hH, horth _ (wv β).2, map_zero]
    rw [hL, hermQuad_smul_add_of_orth hH _ horth']
    by_cases hw0 : ((wv β : W) : ι → ℂ) = 0
    · have hβs : ∀ i, β (some i) = 0 := fun i =>
        Fintype.linearIndependent_iff.mp bW.linearIndependent (fun i => β (some i))
          (Subtype.ext hw0) i
      have hβn : β none ≠ 0 := by
        intro h0
        apply hβ
        funext o
        cases o with
        | none => exact h0
        | some i => exact hβs i
      rw [hw0]
      have : hermQuad H 0 = 0 := by simp [hermQuad]
      rw [this, add_zero]
      exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hβn) hneg
    · have h1 := hW _ (wv β).2 hw0
      rw [hermQuad_neg] at h1
      nlinarith [Complex.normSq_nonneg (β none)]
  have h := card_le_negIndexOn_of_forall_neg H V L
    (fun β => by rw [hL]; exact V.add_mem (V.smul_mem _ hc) (hWV (wv β).2)) hneg'
  rw [Fintype.card_option, Fintype.card_fin, ← hmax] at h
  omega

theorem hermQuad_sum {S : Type*} [Fintype S] (A : S → Matrix ι ι ℂ) (c : ι → ℂ) :
    hermQuad (∑ p, A p) c = ∑ p, hermQuad (A p) c := by
  simp only [hermQuad, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- The pairing with a fixed vector as a linear functional. -/
def hermPairLin (H : Matrix ι ι ℂ) (w : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := hermPair H w c
  map_add' c d := by simp [hermPair, Matrix.mulVec_add, dotProduct_add]
  map_smul' t c := by simp [hermPair, Matrix.mulVec_smul, dotProduct_smul]

/-- **Subadditivity on a hyperplane.** A sum of Hermitian forms has at most one negative square
more than the sum of their negative squares on the kernel of a functional. -/
theorem hermNegIndex_sum_le {S : Type*} [Fintype S] (A : S → Matrix ι ι ℂ)
    (hA : ∀ p, (A p).IsHermitian) (φ : (ι → ℂ) →ₗ[ℂ] ℂ) :
    hermNegIndex (∑ p, A p) ≤ 1 + ∑ p, negIndexOn (A p) (LinearMap.ker φ) := by
  choose W hWV hWr hW using fun p => exists_negIndexOn (A p) (LinearMap.ker φ)
  set b := fun p => Module.finBasis ℂ (W p)
  set F : Unit ⊕ (Σ p, Fin (Module.finrank ℂ (W p))) → (ι → ℂ) →ₗ[ℂ] ℂ := fun j =>
    match j with
    | Sum.inl _ => φ
    | Sum.inr ⟨p, i⟩ => hermPairLin (A p) ((b p i : W p) : ι → ℂ)
  have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker (∑ p, A p) F
    fun c hc => by
      have hcV : c ∈ LinearMap.ker φ := hc (Sum.inl ())
      rw [hermQuad_sum]
      refine Finset.sum_nonneg fun p _ => ?_
      refine hermQuad_nonneg_of_orth_maximal (hA p) (hWV p) (hW p) (hWr p) hcV fun w hw => ?_
      -- orthogonality to a basis extends to its span
      have hw' : w = ∑ i, ((b p).repr ⟨w, hw⟩ i) • ((b p i : W p) : ι → ℂ) := by
        have := congrArg Subtype.val ((b p).sum_repr ⟨w, hw⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hw']
      simp only [hermPair, star_sum, star_smul, sum_dotProduct, smul_dotProduct]
      refine sum_eq_zero fun i _ => ?_
      have := hc (Sum.inr ⟨p, i⟩)
      simp only [F, hermPairLin, LinearMap.coe_mk, AddHom.coe_mk, hermPair] at this
      rw [this, smul_zero]
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma] at h
  simpa [hWr] using h

end Matrices

/-! ### The polar index -/

/-- The total mass `c ↦ Σ_a c_a`; its kernel is the polar hyperplane of the constant direction. -/
def totalMass (ι : Type*) [Fintype ι] : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := ∑ a, c a
  map_add' c d := by simp [sum_add_distrib]
  map_smul' t c := by simp [mul_sum]

variable {G : Type*} [Group G]

/-- The **polar index** of a kernel: its negative squares on mean-zero coefficient vectors. -/
def polarIndex (k : G → ℂ) : ℕ∞ :=
  ⨆ (n : ℕ) (x : Fin n → G), (negIndexOn (gram k x) (LinearMap.ker (totalMass (Fin n))) : ℕ∞)

theorem negIndexOn_le_polarIndex (k : G → ℂ) {n : ℕ} (x : Fin n → G) :
    (negIndexOn (gram k x) (LinearMap.ker (totalMass (Fin n))) : ℕ∞) ≤ polarIndex k :=
  le_iSup₂ (f := fun n (x : Fin n → G) =>
    (negIndexOn (gram k x) (LinearMap.ker (totalMass (Fin n))) : ℕ∞)) n x

theorem polarIndex_le_negIndex (k : G → ℂ) : polarIndex k ≤ negIndex k :=
  iSup₂_le fun _ x =>
    (Nat.cast_le.mpr (negIndexOn_le_hermNegIndex _ _)).trans (hermNegIndex_gram_le_negIndex k x)

/-- The polar hyperplane costs at most one square. -/
theorem negIndex_le_polarIndex_add_one (k : G → ℂ) : negIndex k ≤ polarIndex k + 1 :=
  negIndex_le_iff.mpr fun n x => by
    have h := hermNegIndex_le_negIndexOn_ker_add_one (gram k x) (totalMass (Fin n))
    calc (hermNegIndex (gram k x) : ℕ∞)
        ≤ ((negIndexOn (gram k x) (LinearMap.ker (totalMass (Fin n))) + 1 : ℕ) : ℕ∞) :=
          Nat.cast_le.mpr h
      _ ≤ polarIndex k + 1 := by
          push_cast
          gcongr
          exact negIndexOn_le_polarIndex k x

/-! ### Separable assemblies -/

section Separable

variable {S : Type*} [Fintype S] [DecidableEq S] {H : S → Type*} [∀ p, Group (H p)]

/-- The **separable assembly** of local kernels: `K(g) = Σ_p k_p(g_p)`. -/
def separable (k : ∀ p, H p → ℂ) (g : ∀ p, H p) : ℂ := ∑ p, k p (g p)

omit [DecidableEq S] in
theorem gram_separable (k : ∀ p, H p → ℂ) {n : ℕ} (z : Fin n → ∀ p, H p) :
    gram (separable k) z = ∑ p, gram (k p) fun a => z a p := by
  ext a b
  simp [gram, separable, Matrix.sum_apply]

omit [DecidableEq S] in
/-- **Upper half of the signature formula.** -/
theorem negIndex_separable_le_polarIndex_sum_add_one (k : ∀ p, H p → ℂ)
    (hk : ∀ p, IsHermKernel (k p)) :
    negIndex (separable k) ≤ ∑ p, polarIndex (k p) + 1 := by
  refine negIndex_le_iff.mpr fun n z => ?_
  rw [gram_separable]
  have h := hermNegIndex_sum_le (fun p => gram (k p) fun a => z a p)
    (fun p => gram_isHermitian (hk p) _) (totalMass (Fin n))
  calc (hermNegIndex (∑ p, gram (k p) fun a => z a p) : ℕ∞)
      ≤ ((1 + ∑ p, negIndexOn (gram (k p) fun a => z a p)
          (LinearMap.ker (totalMass (Fin n))) : ℕ) : ℕ∞) := Nat.cast_le.mpr h
    _ = 1 + ∑ p, (negIndexOn (gram (k p) fun a => z a p)
          (LinearMap.ker (totalMass (Fin n))) : ℕ∞) := by push_cast; rfl
    _ ≤ 1 + ∑ p, polarIndex (k p) := by
        gcongr with p
        exact negIndexOn_le_polarIndex (k p) _
    _ = ∑ p, polarIndex (k p) + 1 := add_comm _ _

/-- The axis family: block `q` sits on the `q`-th coordinate, all others at the identity. -/
def axisFamily (n : S → ℕ) (y : ∀ q, Fin (n q) → H q) (i : Σ q, Fin (n q)) : ∀ p, H p :=
  Pi.mulSingle i.1 (y i.1 i.2)

omit [Fintype S] in
/-- Only the `r`-th coordinate of the axis family varies on block `r`. -/
theorem axisFamily_apply_ne (n : S → ℕ) (y : ∀ q, Fin (n q) → H q) {r : S}
    (i : Σ q, Fin (n q)) (h : i.1 ≠ r) : axisFamily n y i r = 1 :=
  Pi.mulSingle_eq_of_ne (Ne.symm h) _

omit [Fintype S] in
theorem axisFamily_apply_self (n : S → ℕ) (y : ∀ q, Fin (n q) → H q) (q : S) (a : Fin (n q)) :
    axisFamily n y ⟨q, a⟩ q = y q a :=
  Pi.mulSingle_eq_same _ _

/-- The Gram form of one local kernel on the axis family: blocks of total mass zero off the
`r`-th axis do not contribute. -/
theorem gramForm_axis (n : S → ℕ) (y : ∀ q, Fin (n q) → H q) (r : S) (f : H r → ℂ)
    (C : (Σ q, Fin (n q)) → ℂ) (hC : ∀ q, ∑ a, C ⟨q, a⟩ = 0) :
    ∑ i, ∑ j, conj (C i) * f ((axisFamily n y i r)⁻¹ * axisFamily n y j r) * C j =
      ∑ a, ∑ b, conj (C ⟨r, a⟩) * f ((y r a)⁻¹ * y r b) * C ⟨r, b⟩ := by
  -- the inner sum over `j`: blocks off `r` sit at the identity and have mass zero
  have hinner : ∀ u : H r, ∑ j, f (u * axisFamily n y j r) * C j =
      ∑ b, f (u * y r b) * C ⟨r, b⟩ := by
    intro u
    rw [Fintype.sum_sigma, ← Finset.add_sum_erase _ _ (mem_univ r)]
    have h0 : ∑ q ∈ univ.erase r, ∑ b, f (u * axisFamily n y ⟨q, b⟩ r) * C ⟨q, b⟩ = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      have hqr : q ≠ r := Finset.ne_of_mem_erase hq
      simp_rw [axisFamily_apply_ne n y ⟨q, _⟩ hqr, mul_one]
      rw [← Finset.mul_sum, hC q, mul_zero]
    rw [h0, add_zero]
    simp_rw [axisFamily_apply_self]
  -- the outer sum over `i`
  have hrow : ∀ i, ∑ j, conj (C i) * f ((axisFamily n y i r)⁻¹ * axisFamily n y j r) * C j =
      conj (C i) * ∑ b, f ((axisFamily n y i r)⁻¹ * y r b) * C ⟨r, b⟩ := by
    intro i
    rw [← hinner, Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hrow]
  rw [Fintype.sum_sigma, ← Finset.add_sum_erase _ _ (mem_univ r)]
  have h0 : ∑ q ∈ univ.erase r, ∑ a, conj (C ⟨q, a⟩) *
      ∑ b, f ((axisFamily n y ⟨q, a⟩ r)⁻¹ * y r b) * C ⟨r, b⟩ = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hqr : q ≠ r := Finset.ne_of_mem_erase hq
    simp_rw [axisFamily_apply_ne n y ⟨q, _⟩ hqr, inv_one, one_mul]
    rw [← Finset.sum_mul, ← map_sum, hC q, map_zero, zero_mul]
  rw [h0, add_zero]
  refine sum_congr rfl fun a _ => ?_
  rw [axisFamily_apply_self, Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  ring

/-- **The axes are orthogonal.** On coefficient vectors of total mass zero on every block, the
form of the separable assembly on the axis family is the sum of the local forms. -/
theorem hermQuad_gram_axes (k : ∀ p, H p → ℂ) (n : S → ℕ) (y : ∀ q, Fin (n q) → H q)
    (C : (Σ q, Fin (n q)) → ℂ) (hC : ∀ q, ∑ a, C ⟨q, a⟩ = 0) :
    hermQuad (gram (separable k) (axisFamily n y)) C =
      ∑ r, hermQuad (gram (k r) (y r)) fun a => C ⟨r, a⟩ := by
  simp only [hermQuad_gram, separable]
  rw [← Complex.re_sum]
  congr 1
  have e : ∀ i j, conj (C i) * (∑ r, k r (((axisFamily n y i)⁻¹ * axisFamily n y j) r)) * C j =
      ∑ r, conj (C i) * k r ((axisFamily n y i r)⁻¹ * axisFamily n y j r) * C j := by
    intro i j
    rw [Finset.mul_sum, Finset.sum_mul]
    rfl
  simp_rw [e]
  rw [show (∑ i, ∑ j, ∑ r, conj (C i) * k r ((axisFamily n y i r)⁻¹ * axisFamily n y j r) * C j)
      = ∑ r, ∑ i, ∑ j, conj (C i) * k r ((axisFamily n y i r)⁻¹ * axisFamily n y j r) * C j from
    (sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm]
  exact sum_congr rfl fun r _ => gramForm_axis n y r (k r) C hC

omit [DecidableEq S] in
/-- **Lower half of the signature formula, on families.** Polar negative subspaces of the local
kernels, embedded on their axes, add up. -/
theorem sum_finrank_le_negIndex_separable (k : ∀ p, H p → ℂ) (n : S → ℕ)
    (y : ∀ q, Fin (n q) → H q) (W : ∀ q, Submodule ℂ (Fin (n q) → ℂ))
    (hWV : ∀ q, W q ≤ LinearMap.ker (totalMass (Fin (n q))))
    (hW : ∀ q, IsPosDefOn (-gram (k q) (y q)) (W q)) :
    ((∑ q, Module.finrank ℂ (W q) : ℕ) : ℕ∞) ≤ negIndex (separable k) := by
  classical
  set b := fun q => Module.finBasis ℂ (W q)
  let L : ((Σ q, Fin (Module.finrank ℂ (W q))) → ℂ) →ₗ[ℂ] ((Σ q, Fin (n q)) → ℂ) :=
    { toFun := fun β i => ∑ t, β ⟨i.1, t⟩ * ((b i.1 t : W i.1) : Fin (n i.1) → ℂ) i.2
      map_add' := fun β β' => funext fun i => by simp [add_mul, sum_add_distrib]
      map_smul' := fun s β => funext fun i => by simp [mul_assoc, mul_sum] }
  set wv : ((Σ q, Fin (Module.finrank ℂ (W q))) → ℂ) → ∀ q, W q :=
    fun β q => ∑ t, β ⟨q, t⟩ • b q t
  have hwv : ∀ β q, ((wv β q : W q) : Fin (n q) → ℂ) = fun a => L β ⟨q, a⟩ := fun β q => by
    funext a; simp [wv, Finset.sum_apply]; rfl
  have hmass : ∀ β q, ∑ a, L β ⟨q, a⟩ = 0 := fun β q => by
    have h := hWV q (wv β q).2
    rw [LinearMap.mem_ker, hwv] at h
    exact h
  have hneg : ∀ β, β ≠ 0 → hermQuad (gram (separable k) (axisFamily n y)) (L β) < 0 := by
    intro β hβ
    rw [hermQuad_gram_axes k n y (L β) (hmass β)]
    obtain ⟨⟨q, t⟩, hqt⟩ : ∃ i, β i ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (funext h)
    have hw0 : ((wv β q : W q) : Fin (n q) → ℂ) ≠ 0 := fun h0 => hqt
      (Fintype.linearIndependent_iff.mp (b q).linearIndependent (fun t => β ⟨q, t⟩)
        (Subtype.ext h0) t)
    have hle : ∀ r, hermQuad (gram (k r) (y r)) (fun a => L β ⟨r, a⟩) ≤ 0 := fun r => by
      rw [← hwv]
      by_cases hr : ((wv β r : W r) : Fin (n r) → ℂ) = 0
      · rw [hr]; simp [hermQuad]
      · have := hW r _ (wv β r).2 hr
        rw [hermQuad_neg] at this
        linarith
    have hlt : hermQuad (gram (k q) (y q)) (fun a => L β ⟨q, a⟩) < 0 := by
      rw [← hwv]
      have := hW q _ (wv β q).2 hw0
      rw [hermQuad_neg] at this
      linarith
    calc ∑ r, hermQuad (gram (k r) (y r)) (fun a => L β ⟨r, a⟩)
        < ∑ _r : S, (0 : ℝ) := Finset.sum_lt_sum (fun r _ => hle r) ⟨q, mem_univ _, hlt⟩
      _ = 0 := by simp
  have h := card_le_hermNegIndex_of_forall_neg _ L hneg
  rw [Fintype.card_sigma] at h
  simp only [Fintype.card_fin] at h
  exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex _ _)

/-- Every local polar index is at most the global index. -/
theorem polarIndex_le_negIndex_separable (k : ∀ p, H p → ℂ) (p : S) :
    polarIndex (k p) ≤ negIndex (separable k) := by
  refine iSup₂_le fun m x => ?_
  obtain ⟨Wp, hWpV, hWpr, hWp⟩ := exists_negIndexOn (gram (k p) x)
    (LinearMap.ker (totalMass (Fin m)))
  -- block `p` carries `x`; every other block carries no negative subspace
  set y : ∀ q, Fin m → H q := fun q => if h : q = p then h ▸ x else fun _ => 1
  set W : S → Submodule ℂ (Fin m → ℂ) := fun q => if q = p then Wp else ⊥
  have hWV : ∀ q, W q ≤ LinearMap.ker (totalMass (Fin m)) := fun q => by
    by_cases hq : q = p
    · simp only [W, if_pos hq]; exact hWpV
    · simp only [W, if_neg hq]; exact bot_le
  have hW : ∀ q, IsPosDefOn (-gram (k q) (y q)) (W q) := fun q => by
    by_cases hq : q = p
    · subst hq
      simp only [W, y, if_pos rfl, dif_pos rfl]
      exact hWp
    · intro w hw hw0
      simp only [W, if_neg hq, Submodule.mem_bot] at hw
      exact absurd hw hw0
  have h := sum_finrank_le_negIndex_separable k (fun _ => m) y W hWV hW
  rw [Finset.sum_eq_single p (fun q _ hq => by simp [W, if_neg hq]) (fun h => absurd (mem_univ p) h)]
    at h
  have hWp' : W p = Wp := if_pos rfl
  rw [hWp', hWpr] at h
  exact h

/-- **Lower half of the signature formula.** -/
theorem polarIndex_sum_le_negIndex_separable (k : ∀ p, H p → ℂ) :
    ∑ p, polarIndex (k p) ≤ negIndex (separable k) := by
  rcases eq_or_ne (negIndex (separable k)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hfin : ∀ p, polarIndex (k p) < ⊤ := fun p =>
    (polarIndex_le_negIndex_separable k p).trans_lt (lt_top_iff_ne_top.mpr htop)
  have hatt : ∀ p, ∃ (m : ℕ) (x : Fin m → H p),
      (negIndexOn (gram (k p) x) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) = polarIndex (k p) := by
    intro p
    have h' : ⨆ q : (Σ m : ℕ, Fin m → H p),
        (negIndexOn (gram (k p) q.2) (LinearMap.ker (totalMass (Fin q.1))) : ℕ∞) =
          polarIndex (k p) := by
      rw [polarIndex, iSup_sigma]
    haveI : Nonempty (Σ m : ℕ, Fin m → H p) := ⟨⟨0, Fin.elim0⟩⟩
    obtain ⟨⟨m, x⟩, hx⟩ := ENat.exists_eq_iSup_of_lt_top (h'.symm ▸ hfin p)
    exact ⟨m, x, hx.trans h'⟩
  choose m x hx using hatt
  choose W hWV hWr hW using fun p =>
    exists_negIndexOn (gram (k p) (x p)) (LinearMap.ker (totalMass (Fin (m p))))
  have h := sum_finrank_le_negIndex_separable k m x W hWV hW
  calc ∑ p, polarIndex (k p)
      = ∑ p, ((negIndexOn (gram (k p) (x p)) (LinearMap.ker (totalMass (Fin (m p)))) : ℕ) : ℕ∞) :=
        sum_congr rfl fun p _ => (hx p).symm
    _ = ((∑ p, Module.finrank ℂ (W p) : ℕ) : ℕ∞) := by
        push_cast
        exact sum_congr rfl fun p _ => by rw [hWr p]
    _ ≤ _ := h

end Separable

/-! ### The negative log-height -/

/-- The kernel `m ↦ −|m|` on `ℤ`. -/
def negAbsKernel (m : Multiplicative ℤ) : ℂ := -((|Multiplicative.toAdd m| : ℤ) : ℂ)

theorem isHermKernel_negAbsKernel : IsHermKernel negAbsKernel := fun m => by
  simp [negAbsKernel, abs_neg]

/-- The minimum kernel on `ℕ` is a sum of squares: `min(a, b) = #{t < M : t < a, t < b}`. -/
theorem sum_mul_min_eq {ι : Type*} [Fintype ι] (w : ι → ℕ) (c : ι → ℂ) {M : ℕ}
    (hM : ∀ a, w a ≤ M) :
    ∑ a, ∑ b, conj (c a) * ((min (w a) (w b) : ℕ) : ℂ) * c b =
      ∑ t ∈ range M, ((normSq (∑ a, if t < w a then c a else 0) : ℝ) : ℂ) := by
  have hmin : ∀ a b, ((min (w a) (w b) : ℕ) : ℂ) =
      ∑ t ∈ range M, (if t < w a then (1 : ℂ) else 0) * (if t < w b then 1 else 0) := by
    intro a b
    have hf : (range M).filter (fun t => t < w a ∧ t < w b) = range (min (w a) (w b)) := by
      ext t
      simp only [mem_filter, mem_range, lt_min_iff]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h.1 (hM a), h⟩⟩
    rw [← card_range (min (w a) (w b)), ← hf, card_filter]
    push_cast
    refine sum_congr rfl fun t _ => ?_
    split_ifs <;> simp_all
  calc ∑ a, ∑ b, conj (c a) * ((min (w a) (w b) : ℕ) : ℂ) * c b
      = ∑ a, ∑ b, ∑ t ∈ range M, conj (if t < w a then c a else 0) *
          (if t < w b then c b else 0) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        rw [hmin, mul_sum, sum_mul]
        refine sum_congr rfl fun t _ => ?_
        split_ifs <;> simp
    _ = ∑ a, ∑ t ∈ range M, ∑ b, conj (if t < w a then c a else 0) *
          (if t < w b then c b else 0) := sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ t ∈ range M, ∑ a, ∑ b, conj (if t < w a then c a else 0) *
          (if t < w b then c b else 0) := Finset.sum_comm
    _ = ∑ t ∈ range M, ((normSq (∑ a, if t < w a then c a else 0) : ℝ) : ℂ) := by
        refine sum_congr rfl fun t _ => ?_
        rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]

/-- **`−|m|` is a sum of squares on the polar hyperplane.** With `w = z − L ≥ 0`,
`−|z_b − z_a| = 2 min(w_a, w_b) − w_a − w_b`; the linear terms cancel against the total mass and
the minimum kernel is a sum of squares of the tail sums `Σ_{w_a > t} c_a`. -/
theorem hermQuad_gram_negAbsKernel_eq {n : ℕ} (x : Fin n → Multiplicative ℤ) (c : Fin n → ℂ)
    (hc : ∑ a, c a = 0) : ∃ w : Fin n → ℕ,
      (∀ a b, (w a : ℤ) - w b = Multiplicative.toAdd (x a) - Multiplicative.toAdd (x b)) ∧
      hermQuad (gram negAbsKernel x) c =
        2 * ∑ t ∈ range (∑ b, w b), normSq (∑ a, if t < w a then c a else 0) := by
  set z : Fin n → ℤ := fun a => Multiplicative.toAdd (x a)
  set L : ℤ := -∑ a, |z a|
  have hL : ∀ a, L ≤ z a := fun a => by
    have h1 := Finset.single_le_sum (f := fun a => |z a|) (fun _ _ => abs_nonneg _) (mem_univ a)
    have h2 := neg_abs_le (z a)
    simp only [L]
    linarith
  set w : Fin n → ℕ := fun a => (z a - L).toNat
  have hw : ∀ a, (w a : ℤ) = z a - L := fun a => Int.toNat_of_nonneg (by linarith [hL a])
  have hentry : ∀ a b, negAbsKernel ((x a)⁻¹ * x b) =
      2 * ((min (w a) (w b) : ℕ) : ℂ) - (w a : ℂ) - (w b : ℂ) := by
    intro a b
    have h1 : Multiplicative.toAdd ((x a)⁻¹ * x b) = (w b : ℤ) - w a := by
      rw [hw, hw, toAdd_mul, toAdd_inv]
      simp only [z]
      ring
    have h2 : |((w b : ℤ) - w a)| = (w a : ℤ) + w b - 2 * ((min (w a) (w b) : ℕ) : ℤ) := by
      rcases le_total (w a) (w b) with h | h
      · have h' : (0 : ℤ) ≤ (w b : ℤ) - w a := sub_nonneg.mpr (by exact_mod_cast h)
        rw [min_eq_left h, abs_of_nonneg h']
        ring
      · have h' : (w b : ℤ) - w a ≤ 0 := sub_nonpos.mpr (by exact_mod_cast h)
        rw [min_eq_right h, abs_of_nonpos h']
        ring
    simp only [negAbsKernel, h1, h2]
    rw [show ((min (w a) (w b) : ℕ) : ℂ) = (((min (w a) (w b) : ℕ) : ℤ) : ℂ) by norm_cast]
    push_cast
    ring
  have hlin1 : ∑ a, ∑ b, conj (c a) * (w a : ℂ) * c b = 0 := by
    refine sum_eq_zero fun a _ => ?_
    rw [← mul_sum, hc, mul_zero]
  have hlin2 : ∑ a, ∑ b, conj (c a) * (w b : ℂ) * c b = 0 := by
    simp_rw [mul_assoc]
    rw [← sum_mul_sum]
    have : ∑ a, conj (c a) = 0 := by rw [← map_sum, hc, map_zero]
    rw [this, zero_mul]
  have hM : ∀ a, w a ≤ ∑ b, w b := fun a =>
    Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ a)
  have hform : ∑ a, ∑ b, conj (c a) * negAbsKernel ((x a)⁻¹ * x b) * c b =
      2 * ∑ t ∈ range (∑ b, w b), ((normSq (∑ a, if t < w a then c a else 0) : ℝ) : ℂ) := by
    rw [← sum_mul_min_eq w c hM]
    calc ∑ a, ∑ b, conj (c a) * negAbsKernel ((x a)⁻¹ * x b) * c b
        = ∑ a, ∑ b, (2 * (conj (c a) * ((min (w a) (w b) : ℕ) : ℂ) * c b) -
            conj (c a) * (w a : ℂ) * c b - conj (c a) * (w b : ℂ) * c b) := by
          refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
          rw [hentry]
          ring
      _ = 2 * (∑ a, ∑ b, conj (c a) * ((min (w a) (w b) : ℕ) : ℂ) * c b) -
            (∑ a, ∑ b, conj (c a) * (w a : ℂ) * c b) -
              ∑ a, ∑ b, conj (c a) * (w b : ℂ) * c b := by
          simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hlin1, hlin2, sub_zero, sub_zero]
  refine ⟨w, fun a b => by rw [hw, hw]; ring, ?_⟩
  rw [hermQuad_gram, hform]
  simp [Complex.re_sum]

/-- **`−|m|` is conditionally positive on `ℤ`**: nonnegative on coefficient vectors of total
mass zero. -/
theorem hermQuad_gram_negAbsKernel_nonneg {n : ℕ} (x : Fin n → Multiplicative ℤ) (c : Fin n → ℂ)
    (hc : ∑ a, c a = 0) : 0 ≤ hermQuad (gram negAbsKernel x) c := by
  obtain ⟨w, -, h⟩ := hermQuad_gram_negAbsKernel_eq x c hc
  rw [h]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => Complex.normSq_nonneg _)

/-- The polar index of `−|m|` is zero. -/
theorem polarIndex_negAbsKernel : polarIndex negAbsKernel = 0 := by
  refine nonpos_iff_eq_zero.mp (iSup₂_le fun n x => ?_)
  rw [negIndexOn_eq_zero_of_nonneg fun c hc => hermQuad_gram_negAbsKernel_nonneg x c hc]
  rfl

/-- The weighted negative log-height `−Σ_p a_p |m_p|` on `ℤ^S`. -/
def negLogHeight {S : Type*} [Fintype S] (a : S → ℝ) (g : S → Multiplicative ℤ) : ℂ :=
  separable (fun p m => (a p : ℂ) * negAbsKernel m) g

/-- **The negative log-height is an index-one Pontryagin state.** For nonnegative weights, not
all zero, `−Σ_p a_p |m_p|` has exactly one negative square: every local constituent is
conditionally positive, and the pole glues them with one square. With `a_p = log p` this is
`−log(nd)` on the `S`-units. -/
theorem negIndex_negLogHeight {S : Type*} [Fintype S] [DecidableEq S] (a : S → ℝ)
    (ha : ∀ p, 0 ≤ a p) {q : S} (hq : 0 < a q) : negIndex (negLogHeight a) = 1 := by
  have hk : ∀ p, IsHermKernel fun m : Multiplicative ℤ => (a p : ℂ) * negAbsKernel m :=
    fun p m => by
      show (a p : ℂ) * negAbsKernel m⁻¹ = conj ((a p : ℂ) * negAbsKernel m)
      rw [isHermKernel_negAbsKernel m, map_mul, Complex.conj_ofReal]
  have hpolar : ∀ p, polarIndex (fun m : Multiplicative ℤ => (a p : ℂ) * negAbsKernel m) = 0 := by
    intro p
    refine nonpos_iff_eq_zero.mp (iSup₂_le fun n x => ?_)
    rw [negIndexOn_eq_zero_of_nonneg fun c hc => ?_]
    · rfl
    · have h := hermQuad_gram_negAbsKernel_nonneg x c hc
      rw [hermQuad_gram] at h ⊢
      have e : ∑ i, ∑ j, conj (c i) * ((a p : ℂ) * negAbsKernel ((x i)⁻¹ * x j)) * c j =
          (a p : ℂ) * ∑ i, ∑ j, conj (c i) * negAbsKernel ((x i)⁻¹ * x j) * c j := by
        simp only [Finset.mul_sum]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
      rw [e, Complex.re_ofReal_mul]
      exact mul_nonneg (ha p) h
  have hsep : negLogHeight a = separable fun p m => (a p : ℂ) * negAbsKernel m := rfl
  refine le_antisymm ?_ ?_
  · have h := negIndex_separable_le_polarIndex_sum_add_one _ hk
    rw [hsep]
    simpa [hpolar] using h
  · -- two points `0` and `e_q` carry a negative square
    set e : S → Multiplicative ℤ := Pi.mulSingle q (Multiplicative.ofAdd 1)
    have hval : ∀ g : S → Multiplicative ℤ, negLogHeight a g =
        -∑ p, (a p : ℂ) * ((|Multiplicative.toAdd (g p)| : ℤ) : ℂ) := fun g => by
      simp [negLogHeight, separable, negAbsKernel, sum_neg_distrib]
    have he : negLogHeight a e = -(a q : ℂ) := by
      rw [hval, Finset.sum_eq_single q]
      · simp [e]
      · intro p _ hp; simp [e, Pi.mulSingle_eq_of_ne hp]
      · exact fun h => absurd (mem_univ q) h
    have heinv : negLogHeight a e⁻¹ = -(a q : ℂ) := by
      rw [hval, Finset.sum_eq_single q]
      · simp [e]
      · intro p _ hp; simp [e, Pi.mulSingle_eq_of_ne hp]
      · exact fun h => absurd (mem_univ q) h
    have h1 : negLogHeight a 1 = 0 := by simp [hval]
    have hneg : hermQuad (gram (negLogHeight a) ![1, e]) ![1, 1] < 0 := by
      rw [hermQuad_gram]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        inv_one, one_mul, inv_mul_cancel, mul_one, map_one, he, h1]
      rw [heinv]
      simp
      linarith
    have := card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h
    simpa using this

end GaloisForLFunctions.AdelicKreinGeometry
