import Mathlib
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex

/-!
# Balanced defect, zero index, recurrent boundary, open history

The doubled operator `Tₙ = Sⁿ ⊕ S*ⁿ` on `H ⊕ H` has equal initial and final defect projections of
rank `n`, hence index zero and vanishing boundary class, while its unsigned defect energy `2n`
diverges.  Signed difference invariants cancel balanced positive defects; the ordered pair of defect
projections does not.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal InnerProductSpace

noncomputable section

/-- The doubled Hardy space `H ⊕ H`, with the `ℓ²` direct-sum inner product. -/
abbrev ToeplitzPair : Type := WithLp 2 (ToeplitzSpace × ToeplitzSpace)

/-- The block-diagonal operator `A ⊕ B` on the doubled Hardy space. -/
def pairOp (A B : ToeplitzSpace →L[ℂ] ToeplitzSpace) : ToeplitzPair →L[ℂ] ToeplitzPair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ToeplitzSpace ToeplitzSpace).symm.toContinuousLinearMap ∘L
    ((A.prodMap B) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ ToeplitzSpace ToeplitzSpace).toContinuousLinearMap)

@[simp] theorem pairOp_fst (A B : ToeplitzSpace →L[ℂ] ToeplitzSpace) (x : ToeplitzPair) :
    (pairOp A B x).ofLp.1 = A x.ofLp.1 := rfl

@[simp] theorem pairOp_snd (A B : ToeplitzSpace →L[ℂ] ToeplitzSpace) (x : ToeplitzPair) :
    (pairOp A B x).ofLp.2 = B x.ofLp.2 := rfl

theorem pairOp_ext {A B A' B' : ToeplitzSpace →L[ℂ] ToeplitzSpace}
    (hA : A = A') (hB : B = B') : pairOp A B = pairOp A' B' := by
  rw [hA, hB]

theorem pairOp_one : pairOp 1 1 = 1 := by
  ext x
  rfl

theorem pairOp_comp (A B A' B' : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    pairOp A B ∘L pairOp A' B' = pairOp (A ∘L A') (B ∘L B') := by
  ext x
  rfl

theorem pairOp_sub (A B A' B' : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    pairOp A B - pairOp A' B' = pairOp (A - A') (B - B') := by
  ext x
  rfl

/-- **The adjoint of a block-diagonal operator is the block diagonal of the adjoints.** -/
theorem adjoint_pairOp (A B : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    ContinuousLinearMap.adjoint (pairOp A B)
      = pairOp (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.adjoint B) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, pairOp_fst, pairOp_snd,
    pairOp_fst, pairOp_snd, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

theorem toeplitzPair_ext {x y : ToeplitzPair}
    (h1 : x.ofLp.1 = y.ofLp.1) (h2 : x.ofLp.2 = y.ofLp.2) : x = y := by
  have hpair : x.ofLp = y.ofLp := Prod.ext h1 h2
  calc x = WithLp.toLp 2 x.ofLp := rfl
    _ = WithLp.toLp 2 y.ofLp := by rw [hpair]
    _ = y := rfl

/-! ## The doubled operator and its two defects -/

/-- The doubled operator `Tₙ = Sⁿ ⊕ S*ⁿ`, equation (1). -/
def doubledShift (n : ℕ) : ToeplitzPair →L[ℂ] ToeplitzPair := pairOp (shiftOp n) (backOp n)

theorem adjoint_backOp (n : ℕ) : ContinuousLinearMap.adjoint (backOp n) = shiftOp n := by
  rw [← adjoint_shiftOp, ContinuousLinearMap.adjoint_adjoint]

theorem adjoint_doubledShift (n : ℕ) :
    ContinuousLinearMap.adjoint (doubledShift n) = pairOp (backOp n) (shiftOp n) := by
  rw [doubledShift, adjoint_pairOp, adjoint_shiftOp, adjoint_backOp]

theorem shiftOp_comp_backOp (n : ℕ) :
    shiftOp n ∘L backOp n = 1 - defectOp n := by
  rw [defectOp, ContinuousLinearMap.one_def]
  abel

/-- **Clause 2, initial defect.**  `1 − Tₙ*Tₙ = 0 ⊕ Dₙ`. -/
theorem initialDefect_eq (n : ℕ) :
    1 - ContinuousLinearMap.adjoint (doubledShift n) ∘L doubledShift n
      = pairOp 0 (defectOp n) := by
  rw [adjoint_doubledShift, doubledShift, pairOp_comp, backOp_comp_shiftOp, shiftOp_comp_backOp,
    ← pairOp_one, pairOp_sub]
  refine pairOp_ext ?_ ?_
  · rw [ContinuousLinearMap.one_def, sub_self]
  · abel

/-- **Clause 2, final defect.**  `1 − TₙTₙ* = Dₙ ⊕ 0`. -/
theorem finalDefect_eq (n : ℕ) :
    1 - doubledShift n ∘L ContinuousLinearMap.adjoint (doubledShift n)
      = pairOp (defectOp n) 0 := by
  rw [adjoint_doubledShift, doubledShift, pairOp_comp, backOp_comp_shiftOp, shiftOp_comp_backOp,
    ← pairOp_one, pairOp_sub]
  refine pairOp_ext ?_ ?_
  · abel
  · rw [ContinuousLinearMap.one_def, sub_self]

/-! ## Ranks of the two defects -/

/-- The range of `0 ⊕ D` is carried isomorphically onto the range of `D` by the second
projection. -/
def rangePairZeroEquiv (D : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    LinearMap.range (pairOp 0 D).toLinearMap ≃ₗ[ℂ] LinearMap.range D.toLinearMap where
  toFun x := ⟨((x : ToeplitzPair)).ofLp.2, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y.ofLp.2, by rw [← hy]; rfl⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun w := ⟨WithLp.toLp 2 (0, (w : ToeplitzSpace)), by
    obtain ⟨u, hu⟩ := w.2
    exact ⟨WithLp.toLp 2 (0, u), by
      refine toeplitzPair_ext ?_ ?_
      · rfl
      · exact hu⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.2
    refine toeplitzPair_ext ?_ ?_
    · show (0 : ToeplitzSpace) = ((x : ToeplitzPair)).ofLp.1
      rw [← hy]
      rfl
    · rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- The range of `D ⊕ 0` is carried isomorphically onto the range of `D` by the first
projection. -/
def rangePairZeroEquiv' (D : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    LinearMap.range (pairOp D 0).toLinearMap ≃ₗ[ℂ] LinearMap.range D.toLinearMap where
  toFun x := ⟨((x : ToeplitzPair)).ofLp.1, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y.ofLp.1, by rw [← hy]; rfl⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun w := ⟨WithLp.toLp 2 ((w : ToeplitzSpace), 0), by
    obtain ⟨u, hu⟩ := w.2
    exact ⟨WithLp.toLp 2 (u, 0), by
      refine toeplitzPair_ext ?_ ?_
      · exact hu
      · rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.2
    refine toeplitzPair_ext ?_ ?_
    · rfl
    · show (0 : ToeplitzSpace) = ((x : ToeplitzPair)).ofLp.2
      rw [← hy]
      rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- **Clause 3.**  Both defects have rank `n`. -/
theorem finrank_initialDefect (n : ℕ) :
    Module.finrank ℂ (LinearMap.range (pairOp 0 (defectOp n)).toLinearMap) = n := by
  rw [(rangePairZeroEquiv (defectOp n)).finrank_eq, range_defectOp, finrank_defectSubmodule]

theorem finrank_finalDefect (n : ℕ) :
    Module.finrank ℂ (LinearMap.range (pairOp (defectOp n) 0).toLinearMap) = n := by
  rw [(rangePairZeroEquiv' (defectOp n)).finrank_eq, range_defectOp, finrank_defectSubmodule]

/-! ## Kernel, cokernel and index -/

theorem shiftOp_injective (n : ℕ) : Function.Injective (shiftOp n) := fun _ _ hab =>
  (shiftIsom n).injective hab

theorem ker_backOp (n : ℕ) :
    LinearMap.ker (backOp n).toLinearMap = defectSubmodule n := by
  ext f
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hf k hk
    have h1 := congrArg (fun g : ToeplitzSpace => (g : ℕ → ℂ) (k - n)) hf
    have h2 : k - n + n = k := by omega
    simp only [backOp_apply, h2, lp.coeFn_zero, Pi.zero_apply] at h1
    exact h1
  · intro hf
    ext k
    show (f : ℕ → ℂ) (k + n) = 0
    exact hf (k + n) (by omega)

theorem backOp_surjective (n : ℕ) : Function.Surjective (backOp n) := by
  intro f
  refine ⟨shiftOp n f, ?_⟩
  ext k
  show shiftFun n (f : ℕ → ℂ) (k + n) = (f : ℕ → ℂ) k
  rw [shiftFun_add]

/-- **Clause 1, kernel.**  `ker Tₙ = 0 ⊕ ker S*ⁿ`, an `n`-dimensional space. -/
def kerDoubledEquiv (n : ℕ) :
    LinearMap.ker (doubledShift n).toLinearMap ≃ₗ[ℂ] defectSubmodule n where
  toFun x := ⟨((x : ToeplitzPair)).ofLp.2, by
    have hx : doubledShift n (x : ToeplitzPair) = 0 := x.2
    have h2 : backOp n ((x : ToeplitzPair)).ofLp.2 = 0 :=
      congrArg (fun z : ToeplitzPair => z.ofLp.2) hx
    rw [← ker_backOp n]
    exact h2⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun w := ⟨WithLp.toLp 2 (0, (w : ToeplitzSpace)), by
    show doubledShift n (WithLp.toLp 2 (0, (w : ToeplitzSpace))) = 0
    refine toeplitzPair_ext ?_ ?_
    · show shiftOp n 0 = (0 : ToeplitzPair).ofLp.1
      simp
    · show backOp n (w : ToeplitzSpace) = (0 : ToeplitzPair).ofLp.2
      have : (w : ToeplitzSpace) ∈ LinearMap.ker (backOp n).toLinearMap := by
        rw [ker_backOp]; exact w.2
      simpa using this⟩
  left_inv x := by
    apply Subtype.ext
    have hx : doubledShift n (x : ToeplitzPair) = 0 := x.2
    have h1 : shiftOp n ((x : ToeplitzPair)).ofLp.1 = 0 :=
      congrArg (fun z : ToeplitzPair => z.ofLp.1) hx
    refine toeplitzPair_ext ?_ ?_
    · show (0 : ToeplitzSpace) = ((x : ToeplitzPair)).ofLp.1
      refine shiftOp_injective n ?_
      rw [map_zero]
      exact h1.symm
    · rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- The first component, as a linear map on the doubled space. -/
def fstLinear : ToeplitzPair →ₗ[ℂ] ToeplitzSpace where
  toFun x := x.ofLp.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cokernel projection of the doubled operator. -/
def doubledCokerMap (n : ℕ) : ToeplitzPair →ₗ[ℂ] (defectSubmodule n) :=
  (defectMap n).comp fstLinear

theorem doubledCokerMap_surjective (n : ℕ) : Function.Surjective (doubledCokerMap n) := by
  intro w
  obtain ⟨a, ha⟩ := defectMap_surjective n w
  exact ⟨WithLp.toLp 2 (a, 0), ha⟩

theorem ker_doubledCokerMap (n : ℕ) :
    LinearMap.ker (doubledCokerMap n) = LinearMap.range (doubledShift n).toLinearMap := by
  ext x
  constructor
  · intro hx
    have h1 : x.ofLp.1 ∈ LinearMap.ker (defectMap n) := hx
    rw [← range_shiftOp] at h1
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := backOp_surjective n x.ofLp.2
    exact ⟨WithLp.toLp 2 (a, b), toeplitzPair_ext ha hb⟩
  · rintro ⟨y, rfl⟩
    show defectMap n (shiftOp n y.ofLp.1) = 0
    have hmem : shiftOp n y.ofLp.1 ∈ LinearMap.range (shiftOp n).toLinearMap :=
      ⟨y.ofLp.1, rfl⟩
    rw [range_shiftOp] at hmem
    exact hmem

/-- **Clause 1, cokernel.**  `coker Tₙ = coker Sⁿ ⊕ 0`, an `n`-dimensional space. -/
def cokerDoubledEquiv (n : ℕ) :
    (ToeplitzPair ⧸ LinearMap.range (doubledShift n).toLinearMap) ≃ₗ[ℂ] (defectSubmodule n) :=
  (Submodule.quotEquivOfEq _ _ (ker_doubledCokerMap n).symm).trans
    (LinearMap.quotKerEquivOfSurjective (doubledCokerMap n) (doubledCokerMap_surjective n))

theorem finrank_ker_doubledShift (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker (doubledShift n).toLinearMap) = n := by
  rw [(kerDoubledEquiv n).finrank_eq, finrank_defectSubmodule]

theorem finrank_coker_doubledShift (n : ℕ) :
    Module.finrank ℂ (ToeplitzPair ⧸ LinearMap.range (doubledShift n).toLinearMap) = n := by
  rw [(cokerDoubledEquiv n).finrank_eq, finrank_defectSubmodule]

/-- The Fredholm index of the doubled operator. -/
def doubledIndex (n : ℕ) : ℤ :=
  (Module.finrank ℂ (LinearMap.ker (doubledShift n).toLinearMap) : ℤ)
    - (Module.finrank ℂ (ToeplitzPair ⧸ LinearMap.range (doubledShift n).toLinearMap) : ℤ)

/-- **Clause 4.**  The index of the doubled operator vanishes identically. -/
theorem doubledIndex_eq_zero (n : ℕ) : doubledIndex n = 0 := by
  rw [doubledIndex, finrank_ker_doubledShift, finrank_coker_doubledShift, sub_self]

/-! ## Symbol, boundary class and defect energy -/

/-- The Toeplitz boundary symbol of the doubled operator, equation (3). -/
noncomputable def doubledSymbol (n : ℕ) (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((z ^ n : Circle) : ℂ), ((z⁻¹ ^ n : Circle) : ℂ)]

/-- **Clause 6.**  The symbol determinant is identically one, so the symbol has zero winding and the
stable boundary class vanishes. -/
theorem det_doubledSymbol (n : ℕ) (z : Circle) : (doubledSymbol n z).det = 1 := by
  rw [doubledSymbol, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/-- The signed boundary class of the doubled operator: `[Kₙ] − [Cₙ]` evaluated by rank. -/
def defectClass (n : ℕ) : ℤ :=
  (Module.finrank ℂ (LinearMap.range (pairOp 0 (defectOp n)).toLinearMap) : ℤ)
    - (Module.finrank ℂ (LinearMap.range (pairOp (defectOp n) 0).toLinearMap) : ℤ)

/-- **Clause 6, computational form.**  `[Kₙ] − [Cₙ] = n − n = 0`. -/
theorem defectClass_eq_zero (n : ℕ) : defectClass n = 0 := by
  rw [defectClass, finrank_initialDefect, finrank_finalDefect, sub_self]

theorem defectClass_eq_doubledIndex (n : ℕ) : defectClass n = doubledIndex n := by
  rw [defectClass_eq_zero, doubledIndex_eq_zero]

/-- The unsigned defect energy `E(Tₙ) = Tr Kₙ + Tr Cₙ`, equation (4). -/
def defectEnergy (n : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (pairOp 0 (defectOp n)).toLinearMap)
    + Module.finrank ℂ (LinearMap.range (pairOp (defectOp n) 0).toLinearMap)

/-- **Clause 7.**  `E(Tₙ) = 2n`. -/
theorem defectEnergy_eq (n : ℕ) : defectEnergy n = 2 * n := by
  rw [defectEnergy, finrank_initialDefect, finrank_finalDefect]
  ring

/-! ## The finite boundary observer of the doubled operator -/

/-- The doubled root-of-unity boundary observer, equation (5). -/
noncomputable def doubledObserver (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![boundaryObserver m n, (boundaryObserver m n)⁻¹]

/-- **Clause 8, periodicity.** -/
theorem doubledObserver_add (m n : ℕ) (hm : m ≠ 0) :
    doubledObserver m (n + m) = doubledObserver m n := by
  rw [doubledObserver, doubledObserver, boundaryObserver_add m n hm]

theorem matrix_diagonal_one_one : Matrix.diagonal ![(1 : ℂ), 1] = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **Clause 8, exact return.**  Along `n = km` the doubled observer is the identity. -/
theorem doubledObserver_mul (m k : ℕ) (hm : m ≠ 0) : doubledObserver m (k * m) = 1 := by
  rw [doubledObserver, boundaryObserver_mul m k hm, inv_one, matrix_diagonal_one_one]

/-- **Clause 8, divergence.**  The unsigned defect energy diverges along the observer returns. -/
theorem defectEnergy_return_tendsto (m : ℕ) (hm : m ≠ 0) :
    Filter.Tendsto (fun k : ℕ => defectEnergy (k * m)) Filter.atTop Filter.atTop := by
  have hfun : (fun k : ℕ => defectEnergy (k * m)) = fun k : ℕ => 2 * (k * m) := by
    funext k
    exact defectEnergy_eq (k * m)
  rw [hfun]
  refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => ?_⟩
  calc b ≤ a := ha
    _ ≤ a * m := Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hm)
    _ ≤ 2 * (a * m) := Nat.le_mul_of_pos_left _ (by norm_num)

/-! ## The abstract cancellation theorem -/

section AbstractCancellation

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- The signed-defect map of equation (6): `δ(a,b) = [a] − [b]`. -/
def signedDefect (φ : M →+ G) (p : M × M) : G := φ p.1 - φ p.2

/-- **Every diagonal pair lies in the kernel of the signed defect.** -/
@[simp] theorem signedDefect_diag (φ : M →+ G) (a : M) : signedDefect φ (a, a) = 0 :=
  sub_self _

/-- **The signed defect is blind to the size of a balanced pair:** all diagonal pairs have the same
signed defect, whatever their weight. -/
theorem signedDefect_diag_eq (φ : M →+ G) (a b : M) :
    signedDefect φ (a, a) = signedDefect φ (b, b) := by
  rw [signedDefect_diag, signedDefect_diag]

/-- **The unsigned energy of a balanced pair is twice its weight**, hence positive as soon as the
weight is, even though the signed defect vanishes. -/
theorem unsigned_energy_of_diag {w : M → ℝ} {a : M} (ha : 0 < w a) :
    signedDefect (0 : M →+ G) (a, a) = 0 ∧ w a + w a = 2 * w a ∧ 0 < w a + w a :=
  ⟨signedDefect_diag _ a, by ring, by linarith⟩

/-- **No invariant factoring through the signed defect can reconstruct the unsigned energy.**  If a
map `F` factors through `δ`, it takes the same value on every balanced pair, while the unsigned
energy of `(a,a)` is `2 w a` and separates weights. -/
theorem no_reconstruction_through_signedDefect {R : Type*} (φ : M →+ G) (F : G → R) (a b : M) :
    F (signedDefect φ (a, a)) = F (signedDefect φ (b, b)) := by
  rw [signedDefect_diag_eq φ a b]

end AbstractCancellation

/-- **The theorem.**  For every `n` the doubled operator has equal `n`-dimensional kernel and
cokernel defects, hence vanishing index and vanishing signed boundary class and unit symbol
determinant, while its unsigned defect energy is `2n`; along every root-of-unity observer return the
observer is the identity while the energy diverges. -/
theorem balanced_defect_zero_index_open_history (n m k : ℕ) (hm : m ≠ 0) :
    1 - ContinuousLinearMap.adjoint (doubledShift n) ∘L doubledShift n = pairOp 0 (defectOp n) ∧
      1 - doubledShift n ∘L ContinuousLinearMap.adjoint (doubledShift n)
        = pairOp (defectOp n) 0 ∧
      Module.finrank ℂ (LinearMap.range (pairOp 0 (defectOp n)).toLinearMap) = n ∧
      Module.finrank ℂ (LinearMap.range (pairOp (defectOp n) 0).toLinearMap) = n ∧
      doubledIndex n = 0 ∧
      (∀ z : Circle, (doubledSymbol n z).det = 1) ∧
      defectClass n = 0 ∧
      defectEnergy n = 2 * n ∧
      doubledObserver m (k * m) = 1 ∧
      defectEnergy (k * m) = 2 * (k * m) :=
  ⟨initialDefect_eq n, finalDefect_eq n, finrank_initialDefect n, finrank_finalDefect n,
    doubledIndex_eq_zero n, det_doubledSymbol n, defectClass_eq_zero n, defectEnergy_eq n,
    doubledObserver_mul m k hm, defectEnergy_eq (k * m)⟩

end

end GaloisForLFunctions.HTGeometry
