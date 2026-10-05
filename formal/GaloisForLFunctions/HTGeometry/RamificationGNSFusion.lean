import GaloisForLFunctions.HTGeometry.RamificationShellFormation
import GaloisForLFunctions.HTGeometry.SquareSummableFrameSynthesis
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert

/-!
# GNS and spectral fusion of a ramification power formation

A splitting `κ ≃ ι ⊕ ξ` of an index set splits `ℓ²(κ)` orthogonally: extension by zero along the
two summands gives isometries `T : ℓ²(ι) → ℓ²(κ)`, `J : ℓ²(ξ) → ℓ²(κ)` with orthogonal ranges whose
sum is everything; `T*` and `J*` are the restrictions, `R = T T*` is the coordinate projection onto
the `ι`-coordinates and `Q = 1 - R = J J*`.

For the power splitting `A_{rm} ≃ A_m ⊔ X_{m,r}`, `T` is `T_r e_k = e_{k^r}`, and with the cyclic
vectors `Ω_{m,σ}(n) = n^{-σ/2}/√S_m(σ)`, `Ω^{ex}(N) = N^{-σ/2}/√C_{m,r}(σ)`:

* `Ω_{rm,σ} = √α T_r Ω_{m,rσ} + √β J Ω^{ex}` and `⟨Ω_{rm,σ}, Q Ω_{rm,σ}⟩ = β`;
* the logarithmic clocks `D e_n = (log n) e_n`, on their maximal domains, satisfy
  `D_{rm} T_r = r T_r D_m` and `D_{rm} ≅ r D_m ⊕ D^{ex}`;
* `S_{rm}(z) = S_m(rz) + C_{m,r}(z)` for `Re z > 1`, hence the characteristic fusion
  `S_{rm}(σ+it)/S_{rm}(σ) = α S_m(r(σ+it))/S_m(rσ) + β C(σ+it)/C(σ)`;
* the heat operators are positive and trace class with `Tr e^{-tD_{rm}} = Tr e^{-rtD_m} +
  Tr e^{-tD^{ex}}`, the traces being `S_{rm}(t)`, `S_m(rt)`, `C_{m,r}(t)`;
* the scalar spectral measure `Σ_n |Ω(n)|² δ_{log n}` of the clock in `Ω_{rm,σ}` is the formation
  law `P_{rm,σ}`; with the marked projection `Q` it reconstructs `α`, `β`, both conditional laws,
  and, with the marked mass `S_{rm}(σ)`, the unnormalized measure.  Without the marked mass the
  absolute scale is lost: `c μ` and `μ` have the same normalization.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationExcess

open _root_.RHTower LpDiagonal

/-! ### Orthogonal splitting of `ℓ²` along a splitting of the index set -/

section Split

variable {κ ι ξ : Type*} (e : κ ≃ ι ⊕ ξ)

theorem summable_sq_of_lp {α : Type*} (a : LpTwo α) : Summable fun i => ‖(a : α → ℂ) i‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp a)
  simpa using this

theorem memℓp_two_of_summable {α : Type*} {f : α → ℂ} (h : Summable fun i => ‖f i‖ ^ 2) :
    Memℓp f 2 :=
  memℓp_gen (by rw [ENNReal.toReal_ofNat]; simpa [Real.rpow_two] using h)

theorem memℓp_elim (a : LpTwo ι) (b : LpTwo ξ) :
    Memℓp (fun k => Sum.elim (a : ι → ℂ) (b : ξ → ℂ) (e k)) 2 := by
  refine memℓp_two_of_summable ?_
  have h : Summable fun x : ι ⊕ ξ => ‖Sum.elim (a : ι → ℂ) (b : ξ → ℂ) x‖ ^ 2 :=
    Summable.sum _ (summable_sq_of_lp a) (summable_sq_of_lp b)
  exact e.summable_iff.2 h

/-- The vector with `ι`-coordinates `a` and `ξ`-coordinates `b`. -/
def extendSum (a : LpTwo ι) (b : LpTwo ξ) : LpTwo κ := ⟨_, memℓp_elim e a b⟩

@[simp] theorem extendSum_apply (a : LpTwo ι) (b : LpTwo ξ) (k : κ) :
    (extendSum e a b : κ → ℂ) k = Sum.elim (a : ι → ℂ) (b : ξ → ℂ) (e k) := rfl

theorem extendSum_symm_inl (a : LpTwo ι) (b : LpTwo ξ) (i : ι) :
    (extendSum e a b : κ → ℂ) (e.symm (Sum.inl i)) = (a : ι → ℂ) i := by simp

theorem extendSum_symm_inr (a : LpTwo ι) (b : LpTwo ξ) (x : ξ) :
    (extendSum e a b : κ → ℂ) (e.symm (Sum.inr x)) = (b : ξ → ℂ) x := by simp

/-- The `ι`-coordinates of a vector. -/
def restrInl (w : LpTwo κ) : LpTwo ι :=
  ⟨fun i => (w : κ → ℂ) (e.symm (Sum.inl i)), memℓp_two_of_summable
    ((summable_sq_of_lp w).comp_injective (e.symm.injective.comp Sum.inl_injective))⟩

/-- The `ξ`-coordinates of a vector. -/
def restrInr (w : LpTwo κ) : LpTwo ξ :=
  ⟨fun x => (w : κ → ℂ) (e.symm (Sum.inr x)), memℓp_two_of_summable
    ((summable_sq_of_lp w).comp_injective (e.symm.injective.comp Sum.inr_injective))⟩

@[simp] theorem restrInl_apply (w : LpTwo κ) (i : ι) :
    (restrInl e w : ι → ℂ) i = (w : κ → ℂ) (e.symm (Sum.inl i)) := rfl

@[simp] theorem restrInr_apply (w : LpTwo κ) (x : ξ) :
    (restrInr e w : ξ → ℂ) x = (w : κ → ℂ) (e.symm (Sum.inr x)) := rfl

theorem extendSum_restr (w : LpTwo κ) : extendSum e (restrInl e w) (restrInr e w) = w := by
  refine lp.ext (funext fun k => ?_)
  rw [extendSum_apply]
  rcases h : e k with i | x
  · rw [Sum.elim_inl, restrInl_apply, ← h, Equiv.symm_apply_apply]
  · rw [Sum.elim_inr, restrInr_apply, ← h, Equiv.symm_apply_apply]

theorem restrInl_extendSum (a : LpTwo ι) (b : LpTwo ξ) : restrInl e (extendSum e a b) = a :=
  lp.ext (funext fun i => by simp)

theorem restrInr_extendSum (a : LpTwo ι) (b : LpTwo ξ) : restrInr e (extendSum e a b) = b :=
  lp.ext (funext fun x => by simp)

theorem inner_extendSum (a a' : LpTwo ι) (b b' : LpTwo ξ) :
    ⟪extendSum e a b, extendSum e a' b'⟫_ℂ = ⟪a, a'⟫_ℂ + ⟪b, b'⟫_ℂ := by
  set G : ι ⊕ ξ → ℂ := fun x =>
    ⟪Sum.elim (a : ι → ℂ) (b : ξ → ℂ) x, Sum.elim (a' : ι → ℂ) (b' : ξ → ℂ) x⟫_ℂ
  have h1 : ⟪extendSum e a b, extendSum e a' b'⟫_ℂ = ∑' k : κ, G (e k) := lp.inner_eq_tsum _ _
  have h2 : ∑' k : κ, G (e k) = ∑' x, G x := e.tsum_eq G
  have hs : Summable (G ∘ Sum.inl) := lp.summable_inner (𝕜 := ℂ) a a'
  have hs' : Summable (G ∘ Sum.inr) := lp.summable_inner (𝕜 := ℂ) b b'
  rw [h1, h2, Summable.tsum_sum hs hs', lp.inner_eq_tsum, lp.inner_eq_tsum]
  rfl

theorem norm_sq_extendSum (a : LpTwo ι) (b : LpTwo ξ) :
    ‖extendSum e a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := congrArg Complex.re (inner_extendSum e a a b b)
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

/-- Extension by zero along the `ι`-coordinates, an isometry. -/
def splitInl : LpTwo ι →ₗᵢ[ℂ] LpTwo κ where
  toFun a := extendSum e a 0
  map_add' a a' := lp.ext (funext fun k => by
    rcases h : e k with i | x <;> simp [h])
  map_smul' c a := lp.ext (funext fun k => by
    rcases h : e k with i | x <;> simp [h])
  norm_map' a := by
    show ‖extendSum e a 0‖ = ‖a‖
    have h := norm_sq_extendSum e a (0 : LpTwo ξ)
    rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
    exact le_antisymm (by nlinarith [norm_nonneg (extendSum e a (0 : LpTwo ξ)), norm_nonneg a])
      (by nlinarith [norm_nonneg (extendSum e a (0 : LpTwo ξ)), norm_nonneg a])

/-- Extension by zero along the `ξ`-coordinates, an isometry. -/
def splitInr : LpTwo ξ →ₗᵢ[ℂ] LpTwo κ where
  toFun b := extendSum e 0 b
  map_add' b b' := lp.ext (funext fun k => by
    rcases h : e k with i | x <;> simp [h])
  map_smul' c b := lp.ext (funext fun k => by
    rcases h : e k with i | x <;> simp [h])
  norm_map' b := by
    show ‖extendSum e 0 b‖ = ‖b‖
    have h := norm_sq_extendSum e (0 : LpTwo ι) b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact le_antisymm (by nlinarith [norm_nonneg (extendSum e (0 : LpTwo ι) b), norm_nonneg b])
      (by nlinarith [norm_nonneg (extendSum e (0 : LpTwo ι) b), norm_nonneg b])

theorem splitInl_apply (a : LpTwo ι) : splitInl e a = extendSum e a 0 := rfl

theorem splitInr_apply (b : LpTwo ξ) : splitInr e b = extendSum e 0 b := rfl

/-- **Orthogonal splitting `ℓ²(κ) = T ℓ²(ι) ⊕ J ℓ²(ξ)`**: the ranges are orthogonal and every vector
is the sum of its two coordinate parts. -/
theorem inner_splitInl_splitInr (a : LpTwo ι) (b : LpTwo ξ) :
    ⟪splitInl e a, splitInr e b⟫_ℂ = 0 := by
  rw [splitInl_apply, splitInr_apply, inner_extendSum, inner_zero_right, inner_zero_left,
    add_zero]

theorem splitInl_add_splitInr (w : LpTwo κ) :
    splitInl e (restrInl e w) + splitInr e (restrInr e w) = w := by
  rw [← extendSum_restr e w]
  refine lp.ext (funext fun k => ?_)
  simp only [splitInl_apply, splitInr_apply, AddSubgroup.coe_add, extendSum_apply,
    restrInl_extendSum, restrInr_extendSum]
  rcases h : e k with i | x <;> simp [h]

theorem inner_splitInl (a : LpTwo ι) (w : LpTwo κ) :
    ⟪splitInl e a, w⟫_ℂ = ⟪a, restrInl e w⟫_ℂ := by
  conv_lhs => rw [← extendSum_restr e w]
  rw [splitInl_apply, inner_extendSum, inner_zero_left, add_zero]

theorem inner_splitInr (b : LpTwo ξ) (w : LpTwo κ) :
    ⟪splitInr e b, w⟫_ℂ = ⟪b, restrInr e w⟫_ℂ := by
  conv_lhs => rw [← extendSum_restr e w]
  rw [splitInr_apply, inner_extendSum, inner_zero_left, zero_add]

/-- The restriction to the `ι`-coordinates, as a bounded operator. -/
def restrInlCLM : LpTwo κ →L[ℂ] LpTwo ι :=
  LinearMap.mkContinuous
    { toFun := restrInl e
      map_add' := fun _ _ => lp.ext (funext fun _ => rfl)
      map_smul' := fun _ _ => lp.ext (funext fun _ => rfl) } 1 fun w => by
    rw [one_mul]
    show ‖restrInl e w‖ ≤ ‖w‖
    have h := norm_sq_extendSum e (restrInl e w) (restrInr e w)
    rw [extendSum_restr] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖restrInr e w‖])

/-- The restriction to the `ξ`-coordinates, as a bounded operator. -/
def restrInrCLM : LpTwo κ →L[ℂ] LpTwo ξ :=
  LinearMap.mkContinuous
    { toFun := restrInr e
      map_add' := fun _ _ => lp.ext (funext fun _ => rfl)
      map_smul' := fun _ _ => lp.ext (funext fun _ => rfl) } 1 fun w => by
    rw [one_mul]
    show ‖restrInr e w‖ ≤ ‖w‖
    have h := norm_sq_extendSum e (restrInl e w) (restrInr e w)
    rw [extendSum_restr] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖restrInl e w‖])

/-- `T* = ` restriction to the `ι`-coordinates. -/
theorem restrInlCLM_apply (w : LpTwo κ) : restrInlCLM e w = restrInl e w := rfl

theorem restrInrCLM_apply (w : LpTwo κ) : restrInrCLM e w = restrInr e w := rfl

theorem adjoint_splitInl :
    ContinuousLinearMap.adjoint (splitInl e).toContinuousLinearMap = restrInlCLM e := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (restrInlCLM e)
    (splitInl e).toContinuousLinearMap).2 fun w a => ?_).symm
  rw [restrInlCLM_apply, ← inner_conj_symm, LinearIsometry.coe_toContinuousLinearMap,
    ← inner_splitInl, inner_conj_symm]

/-- `J* = ` restriction to the `ξ`-coordinates. -/
theorem adjoint_splitInr :
    ContinuousLinearMap.adjoint (splitInr e).toContinuousLinearMap = restrInrCLM e := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (restrInrCLM e)
    (splitInr e).toContinuousLinearMap).2 fun w b => ?_).symm
  rw [restrInrCLM_apply, ← inner_conj_symm, LinearIsometry.coe_toContinuousLinearMap,
    ← inner_splitInr, inner_conj_symm]

/-- The range projection `R = T T*`. -/
def rangeProj : LpTwo κ →L[ℂ] LpTwo κ :=
  (splitInl e).toContinuousLinearMap ∘L
    ContinuousLinearMap.adjoint (splitInl e).toContinuousLinearMap

/-- The defect projection `Q = 1 - R`. -/
def defectProj : LpTwo κ →L[ℂ] LpTwo κ := 1 - rangeProj e

/-- `Q = J J*`: the defect projection keeps exactly the `ξ`-coordinates. -/
theorem defectProj_apply (w : LpTwo κ) : defectProj e w = splitInr e (restrInr e w) := by
  rw [defectProj]
  change w - rangeProj e w = _
  rw [rangeProj, ContinuousLinearMap.comp_apply, adjoint_splitInl]
  change w - splitInl e (restrInl e w) = _
  rw [sub_eq_iff_eq_add']
  exact (splitInl_add_splitInr e w).symm

end Split

/-! ### The power splitting -/

variable {m r : ℕ}

/-- `T_r : ℓ²(A_m) → ℓ²(A_{rm})`, `T_r e_k = e_{k^r}`. -/
abbrev powIsometry (hr : r ≠ 0) : LpTwo (EulerShell m) →ₗᵢ[ℂ] LpTwo (EulerShell (r * m)) :=
  splitInl (shellSplit hr)

/-- The excess inclusion `ℓ²(X_{m,r}) → ℓ²(A_{rm})`. -/
abbrev excessIsometry (hr : r ≠ 0) : LpTwo (ExcessShell m r) →ₗᵢ[ℂ] LpTwo (EulerShell (r * m)) :=
  splitInr (shellSplit hr)

theorem powIsometry_single (hr : r ≠ 0) (k : EulerShell m) :
    powIsometry hr (lp.single 2 k 1) = lp.single 2 (shellPow hr k) 1 := by
  refine lp.ext (funext fun N => ?_)
  rw [powIsometry, splitInl_apply, extendSum_apply]
  rcases h : shellSplit hr N with i | x
  · have hN : N = shellPow hr i := by rw [← shellSplit_symm_inl hr, ← h]; simp
    subst hN
    simp only [Sum.elim_inl, lp.single_apply]
    by_cases hik : i = k
    · subst hik; simp
    · rw [Pi.single_eq_of_ne' (Ne.symm hik), Pi.single_eq_of_ne'
        (fun h' => hik (shellPow_injective hr h'.symm))]
  · have hN : N = x.1 := by rw [← shellSplit_symm_inr hr, ← h]; simp
    simp only [Sum.elim_inr, lp.coeFn_zero, Pi.zero_apply, lp.single_apply]
    rw [Pi.single_eq_of_ne']
    intro hkN
    exact x.2 ⟨k, (shellPow_val hr k).symm.trans (congrArg Subtype.val (hkN.trans hN))⟩

theorem rpow_neg_half_shellPow (hr : r ≠ 0) (k : EulerShell m) (σ : ℝ) :
    ((shellPow hr k : ℕ) : ℝ) ^ (-σ / 2) = ((k : ℕ) : ℝ) ^ (-(r * σ) / 2) := by
  rw [show -σ / 2 = -(σ / 2) by ring, rpow_shellPow hr k (σ / 2)]
  congr 1
  ring

/-! ### Cyclic vectors -/

/-- The excess cyclic vector `Ω^{ex}(N) = N^{-σ/2}/√C_{m,r}(σ)`. -/
def excessVector (m r : ℕ) (σ : ℝ) (hσ : 1 < σ) : LpTwo (ExcessShell m r) :=
  ⟨fun N => ((((N : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (excessSum m r σ) : ℝ) : ℂ), by
    refine memℓp_gen ?_
    refine ((summable_excess m r hσ).div_const (excessSum m r σ)).congr fun N => ?_
    have hN : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hC : 0 ≤ excessSum m r σ := tsum_nonneg fun _ => by positivity
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      div_pow, Real.sq_sqrt hC, ← Real.rpow_natCast, ← Real.rpow_mul hN]
    norm_num⟩

theorem excessVector_apply (m r : ℕ) (σ : ℝ) (hσ : 1 < σ) (N : ExcessShell m r) :
    (excessVector m r σ hσ : ExcessShell m r → ℂ) N =
      ((((N : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (excessSum m r σ) : ℝ) : ℂ) := rfl

theorem norm_sq_excessVector_apply (hm : m ≠ 0) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
    (N : ExcessShell m r) :
    ‖(excessVector m r σ hσ : ExcessShell m r → ℂ) N‖ ^ 2 =
      ((N : ℕ) : ℝ) ^ (-σ) / excessSum m r σ := by
  have hC := excessSum_pos hm hr hσ
  rw [excessVector_apply, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow,
    Real.sq_sqrt hC.le, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem norm_excessVector (hm : m ≠ 0) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    ‖excessVector m r σ hσ‖ = 1 := by
  have hC := excessSum_pos hm hr hσ
  have h : ‖excessVector m r σ hσ‖ ^ 2 = 1 := by
    rw [lp_two_norm_sq_eq_tsum]
    simp_rw [norm_sq_excessVector_apply hm hr hσ]
    rw [tsum_div_const, ← excessSum, div_self hC.ne']
  have := norm_nonneg (excessVector m r σ hσ)
  nlinarith [sq_nonneg (‖excessVector m r σ hσ‖ - 1)]

/-- The shell cyclic vector `Ω_{m,σ}`. -/
abbrev shellVector (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ) : LpTwo (EulerShell m) :=
  (eulerShellSource hm hσ).v

section Fusion

variable (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
include hm hr hσ

omit hσ in
theorem one_le_mul_m : 1 ≤ r * m := by nlinarith

/-- **`(FE.22)`**: `Ω_{rm,σ} = √α T_r Ω_{m,rσ} + √β J Ω^{ex}`. -/
theorem shellVector_fusion :
    shellVector (one_le_mul_m hm hr) hσ =
      ((Real.sqrt (survival m r σ) : ℝ) : ℂ) •
          powIsometry (by omega) (shellVector hm (one_lt_mul_of_two_le hr hσ)) +
        ((Real.sqrt (excessFraction m r σ) : ℝ) : ℂ) •
          excessIsometry (by omega) (excessVector m r σ hσ) := by
  have hr0 : r ≠ 0 := by omega
  have hS := eulerShellSum_pos (one_le_mul_m hm hr) hσ
  have hSm := eulerShellSum_pos hm (one_lt_mul_of_two_le hr hσ)
  have hC := excessSum_pos (m := m) (by omega) hr hσ
  have hsS := Real.sqrt_pos.2 hS
  have hsSm := Real.sqrt_pos.2 hSm
  have hsC := Real.sqrt_pos.2 hC
  refine lp.ext (funext fun N => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    splitInl_apply, splitInr_apply, extendSum_apply]
  rcases h : shellSplit hr0 N with k | x
  · have hN : N = shellPow hr0 k := by rw [← shellSplit_symm_inl hr0, ← h]; simp
    simp only [Sum.elim_inl, lp.coeFn_zero, Pi.zero_apply, mul_zero, add_zero,
      eulerShellSource_v]
    rw [hN, ← Complex.ofReal_mul]
    congr 1
    rw [rpow_neg_half_shellPow hr0, survival, Real.sqrt_div' _ hS.le]
    field_simp
  · have hN : N = x.1 := by rw [← shellSplit_symm_inr hr0, ← h]; simp
    simp only [Sum.elim_inr, lp.coeFn_zero, Pi.zero_apply, mul_zero, zero_add,
      eulerShellSource_v]
    rw [excessVector_apply, hN, ← Complex.ofReal_mul]
    congr 1
    rw [excessFraction, Real.sqrt_div' _ hS.le]
    field_simp

end Fusion

end GaloisForLFunctions.HTGeometry.FormationExcess
