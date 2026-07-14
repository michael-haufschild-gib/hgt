/-
# General Hilbert–Schmidt operators between Hilbert spaces

Mathlib carries no Hilbert–Schmidt / Schatten / trace-class operator theory.  The companion file
`HilbertSchmidt` builds the **coordinate** model — square-summable matrices `K : ι × ι → ℂ`
representing Hilbert–Schmidt operators on the single space `ℓ²(ι)`.  This file builds the
**coordinate-free operator** layer: a continuous linear map `T : E →L[𝕜] F` between inner product
spaces is *Hilbert–Schmidt* when `∑ᵢ ‖T eᵢ‖²` is summable over a Hilbert basis `eᵢ` of `E`, and the
value of that sum is independent of the basis.

The pivot is a single unconditional identity in `ℝ≥0∞` (`hsE_eq_adjoint`): for any Hilbert bases
`b` of `E` and `c` of `F`,
`∑ᵢ ‖T (b i)‖²  =  ∑ⱼ ‖T† (c j)‖²`,
obtained by expanding each `‖T (b i)‖²` by Parseval in the basis `c`, swapping the order of
summation (free in `ℝ≥0∞`), moving `T` across the inner product to its adjoint `T†`, and contracting
by Parseval in the basis `b`.  Because the extended-real double sum needs no summability hypothesis,
this one identity yields simultaneously the basis-independence of both summability and value, and the
fact that the adjoint of a Hilbert–Schmidt operator is Hilbert–Schmidt with equal norm.

Proved here:
* `HilbertBasis.tsum_norm_inner_sq`, `HilbertBasis.summable_norm_inner_sq` — Parseval in
  norm-squared form: `∑ᵢ ‖⟨b i, x⟩‖² = ‖x‖²`, and its unconditional summability.
* `ContinuousLinearMap.hsE_eq_adjoint` — the master `ℝ≥0∞` basis/adjoint identity.
* `ContinuousLinearMap.summable_normSq_basis_of_basis`, `tsum_normSq_basis_eq` — square-summability and
  its value transfer between any two Hilbert bases of `E`.
* `ContinuousLinearMap.IsHilbertSchmidt` — the Hilbert–Schmidt predicate; `IsHilbertSchmidt.summable`
  and `isHilbertSchmidt_iff_summable` show it does not depend on the choice of basis.
* `hsNormSq`, `hsNorm`, `hsNormSq_eq` — the basis-independent Hilbert–Schmidt norm.
* `IsHilbertSchmidt.adjoint`, `IsHilbertSchmidt.hsNormSq_adjoint` — the adjoint is Hilbert–Schmidt with
  the same Hilbert–Schmidt norm.
* `isHilbertSchmidt_zero`, `IsHilbertSchmidt.add`, `IsHilbertSchmidt.smul`, `IsHilbertSchmidt.neg`,
  `IsHilbertSchmidt.sub` — the Hilbert–Schmidt operators form a submodule of `E →L[𝕜] F`.
* `IsHilbertSchmidt.comp_left`, `IsHilbertSchmidt.comp_right` — the two-sided ideal property: composing
  a Hilbert–Schmidt operator with any bounded operator stays Hilbert–Schmidt.
* `ContinuousLinearMap.hsInner`, `IsHilbertSchmidt.summable_inner`, `hsInner_self_re` — the
  Hilbert–Schmidt inner product `⟨S, T⟩_HS = ∑ᵢ ⟨S eᵢ, T eᵢ⟩`, convergent for Hilbert–Schmidt `S, T`,
  with `Re⟨T, T⟩_HS = ‖T‖²_HS`.
* `tsum_inner_basis_polarization`, `hsInner_eq_tsum_basis` — polarization: `∑ᵢ ⟨S (b i), T (b i)⟩` is
  a fixed combination of the four Hilbert–Schmidt norms `‖S ± T‖²_HS`, `‖S ∓ i·T‖²_HS`, hence
  independent of the Hilbert basis `b` and equal to `hsInner S T`.
* `hsInner_conj_symm`, `hsInner_add_left`, `hsInner_add_right`, `hsInner_smul_left`,
  `hsInner_smul_right`, `hsNormSq_eq_zero_iff`, `hsNorm_eq_zero_iff`, `norm_hsInner_le`,
  `hsNorm_add_le` — the Hilbert–Schmidt operators carry a genuine inner-product structure:
  sesquilinear conjugate-symmetric positive-definite pairing, Cauchy–Schwarz, triangle inequality.
* `hsInner_adjoint_adjoint` — the adjoint reverses the Hilbert–Schmidt inner product:
  `⟨S†, T†⟩_HS = ⟨T, S⟩_HS`.
* `memℓp_two_of_sq`, `tsum_mul_le_sqrt_mul_sqrt` — Cauchy–Schwarz for real series, through the
  `ℓ²(ι, ℝ)` pairing.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace HilbertBasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*}

/-- **Parseval in norm-squared form.**  `∑ᵢ ‖⟨b i, x⟩‖² = ‖x‖²`: the squared Fourier coefficients of
`x` in a Hilbert basis sum to `‖x‖²`.  The real-scalar shadow of `tsum_inner_mul_inner`. -/
theorem tsum_norm_inner_sq (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ‖(inner 𝕜 (b i) x)‖ ^ 2 = ‖x‖ ^ 2 := by
  have hsum := b.summable_inner_mul_inner x x
  have key := b.tsum_inner_mul_inner x x
  have hre : (RCLike.re (∑' i, (inner 𝕜 x (b i)) * inner 𝕜 (b i) x))
      = ∑' i, RCLike.re ((inner 𝕜 x (b i)) * inner 𝕜 (b i) x) :=
    RCLike.reCLM.map_tsum hsum
  have hpt : ∀ i, RCLike.re ((inner 𝕜 x (b i)) * inner 𝕜 (b i) x) = ‖(inner 𝕜 (b i) x)‖ ^ 2 := by
    intro i
    have hcs : (inner 𝕜 x (b i)) = conj (inner 𝕜 (b i) x) := by rw [← inner_conj_symm]
    rw [hcs, RCLike.conj_mul]; simp
  calc ∑' i, ‖(inner 𝕜 (b i) x)‖ ^ 2
      = ∑' i, RCLike.re ((inner 𝕜 x (b i)) * inner 𝕜 (b i) x) := (tsum_congr hpt).symm
    _ = RCLike.re (∑' i, (inner 𝕜 x (b i)) * inner 𝕜 (b i) x) := hre.symm
    _ = RCLike.re (inner 𝕜 x x) := by rw [key]
    _ = ‖x‖ ^ 2 := by rw [inner_self_eq_norm_sq]

/-- The squared Fourier coefficients `i ↦ ‖⟨b i, x⟩‖²` of any vector are summable (unconditionally). -/
theorem summable_norm_inner_sq (b : HilbertBasis ι 𝕜 E) (x : E) :
    Summable (fun i => ‖(inner 𝕜 (b i) x)‖ ^ 2) := by
  have hs := b.summable_inner_mul_inner x x
  rw [← RCLike.summable_ofReal (𝕜 := 𝕜)]
  refine hs.congr (fun i => ?_)
  have hcs : (inner 𝕜 x (b i)) = conj (inner 𝕜 (b i) x) := by rw [← inner_conj_symm]
  rw [hcs, RCLike.conj_mul]; push_cast; ring

end HilbertBasis

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- A nonnegative real family is `ℝ≥0∞`-summable to a finite value once it is summable. -/
private theorem ofReal_tsum_ne_top {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hs : Summable g) : ∑' i, ENNReal.ofReal (g i) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hg hs]; exact ENNReal.ofReal_ne_top

/-- A nonnegative real family whose `ℝ≥0∞` sum is finite is summable. -/
private theorem summable_of_ofReal_tsum_ne_top {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i)
    (h : ∑' i, ENNReal.ofReal (g i) ≠ ⊤) : Summable g :=
  (ENNReal.summable_toReal h).congr (fun i => ENNReal.toReal_ofReal (hg i))

/-- **The master Hilbert–Schmidt identity.**  For Hilbert bases `b` of `E` and `c` of `F`, the sum of
`‖T (b i)‖²` over `b` equals the sum of `‖T† (c j)‖²` over `c`, as an unconditional identity in
`ℝ≥0∞`: expand each `‖T (b i)‖²` by Parseval in `c`, swap the two sums (free in `ℝ≥0∞`), pass `T`
across the inner product to its adjoint, and contract by Parseval in `b`.  Needing no summability
hypothesis, it delivers basis-independence and the adjoint law at once. -/
theorem hsE_eq_adjoint {ι κ : Type*} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (T : E →L[𝕜] F) :
    ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2) := by
  have row : ∀ i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := by
    intro i
    rw [← c.tsum_norm_inner_sq (T (b i)),
      ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (c.summable_norm_inner_sq (T (b i)))]
  have col : ∀ j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2)
      = ∑' i, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := by
    intro j
    rw [← b.tsum_norm_inner_sq ((ContinuousLinearMap.adjoint T) (c j)),
      ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
        (b.summable_norm_inner_sq ((ContinuousLinearMap.adjoint T) (c j)))]
    refine tsum_congr fun i => ?_
    have hnorm : ‖inner 𝕜 (b i) ((ContinuousLinearMap.adjoint T) (c j))‖ = ‖inner 𝕜 (c j) (T (b i))‖ := by
      calc ‖inner 𝕜 (b i) ((ContinuousLinearMap.adjoint T) (c j))‖
          = ‖inner 𝕜 ((ContinuousLinearMap.adjoint T) (c j)) (b i)‖ := by
            rw [← inner_conj_symm ((ContinuousLinearMap.adjoint T) (c j)) (b i), RCLike.norm_conj]
        _ = ‖inner 𝕜 (c j) (T (b i))‖ := by rw [adjoint_inner_left]
    rw [hnorm]
  calc ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := tsum_congr row
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2) := (tsum_congr col).symm

/-- **Basis transfer of square-summability.**  If `i ↦ ‖T (b i)‖²` is summable over one Hilbert basis
`b` of `E`, it is summable over every Hilbert basis `b'`: route the finiteness through a fixed Hilbert
basis of `F` by the master identity. -/
theorem summable_normSq_basis_of_basis {ι κ : Type*} (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis κ 𝕜 E) (T : E →L[𝕜] F) (hb : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    Summable (fun i' => ‖T (b' i')‖ ^ 2) := by
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  refine summable_of_ofReal_tsum_ne_top (fun i' => by positivity) ?_
  rw [hsE_eq_adjoint b' c T, ← hsE_eq_adjoint b c T]
  exact ofReal_tsum_ne_top (fun i => by positivity) hb

/-- **Basis independence of the value.**  When summable, `∑ᵢ ‖T (b i)‖²` is the same for every Hilbert
basis: both sides equal `ofReal` of the adjoint sum over a common Hilbert basis of `F`, and
`ENNReal.ofReal` is injective on the nonnegatives. -/
theorem tsum_normSq_basis_eq {ι κ : Type*} (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis κ 𝕜 E)
    (T : E →L[𝕜] F) (hb : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    ∑' i, ‖T (b i)‖ ^ 2 = ∑' i', ‖T (b' i')‖ ^ 2 := by
  have hb' := summable_normSq_basis_of_basis b b' T hb
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  have e : ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2) = ∑' i', ENNReal.ofReal (‖T (b' i')‖ ^ 2) :=
    (hsE_eq_adjoint b c T).trans (hsE_eq_adjoint b' c T).symm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hb,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i' => by positivity) hb'] at e
  have := congrArg ENNReal.toReal e
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at this

/-- A canonical Hilbert basis of `E`, chosen from `exists_hilbertBasis`. -/
noncomputable def hsBasis (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : HilbertBasis (exists_hilbertBasis 𝕜 E).choose 𝕜 E :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose

/-- A continuous linear map `T : E →L[𝕜] F` is **Hilbert–Schmidt** when the squared norms of its
values on the canonical Hilbert basis of `E` are summable, `∑ᵢ ‖T eᵢ‖² < ∞`.  `IsHilbertSchmidt.summable`
shows the choice of basis is immaterial. -/
def IsHilbertSchmidt (T : E →L[𝕜] F) : Prop :=
  Summable (fun i => ‖T (hsBasis 𝕜 E i)‖ ^ 2)

/-- **Basis-independence of Hilbert–Schmidt summability.**  A Hilbert–Schmidt `T` has
`i ↦ ‖T (b i)‖²` summable for *every* Hilbert basis `b` of `E`. -/
theorem IsHilbertSchmidt.summable {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) : Summable (fun i => ‖T (b i)‖ ^ 2) :=
  summable_normSq_basis_of_basis (hsBasis 𝕜 E) b T hT

/-- Square-summability over any single Hilbert basis certifies Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_summable {T : E →L[𝕜] F} {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (hb : Summable (fun i => ‖T (b i)‖ ^ 2)) : IsHilbertSchmidt T :=
  summable_normSq_basis_of_basis b (hsBasis 𝕜 E) T hb

/-- Hilbert–Schmidt is equivalent to square-summability over any prescribed Hilbert basis. -/
theorem isHilbertSchmidt_iff_summable {T : E →L[𝕜] F} {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    IsHilbertSchmidt T ↔ Summable (fun i => ‖T (b i)‖ ^ 2) :=
  ⟨fun hT => hT.summable b, fun hb => isHilbertSchmidt_of_summable b hb⟩

/-- The **Hilbert–Schmidt norm squared** `‖T‖²_HS = ∑ᵢ ‖T eᵢ‖²`, evaluated on the canonical Hilbert
basis; `hsNormSq_eq` shows it is the same sum for every Hilbert basis. -/
noncomputable def hsNormSq (T : E →L[𝕜] F) : ℝ := ∑' i, ‖T (hsBasis 𝕜 E i)‖ ^ 2

/-- The **Hilbert–Schmidt norm** `‖T‖_HS = √(∑ᵢ ‖T eᵢ‖²)`. -/
noncomputable def hsNorm (T : E →L[𝕜] F) : ℝ := Real.sqrt (hsNormSq T)

omit [CompleteSpace F] in
theorem hsNormSq_nonneg (T : E →L[𝕜] F) : 0 ≤ hsNormSq T := tsum_nonneg fun _ => by positivity

omit [CompleteSpace F] in
theorem hsNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ hsNorm T := Real.sqrt_nonneg _

/-- The Hilbert–Schmidt norm squared is computed by any Hilbert basis: `‖T‖²_HS = ∑ᵢ ‖T (b i)‖²`. -/
theorem hsNormSq_eq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    hsNormSq T = ∑' i, ‖T (b i)‖ ^ 2 :=
  tsum_normSq_basis_eq (hsBasis 𝕜 E) b T hT

/-- **The adjoint of a Hilbert–Schmidt operator is Hilbert–Schmidt.**  The master identity carries the
finite sum `∑ᵢ ‖T eᵢ‖²` over `E` to `∑ⱼ ‖T† fⱼ‖²` over `F`, which is therefore summable. -/
theorem IsHilbertSchmidt.adjoint {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) := by
  show Summable (fun j => ‖(ContinuousLinearMap.adjoint T) (hsBasis 𝕜 F j)‖ ^ 2)
  refine summable_of_ofReal_tsum_ne_top (fun j => by positivity) ?_
  rw [← hsE_eq_adjoint (hsBasis 𝕜 E) (hsBasis 𝕜 F) T]
  exact ofReal_tsum_ne_top (fun i => by positivity) hT

/-- **The adjoint preserves the Hilbert–Schmidt norm.**  `‖T†‖²_HS = ‖T‖²_HS`: the master identity
equates the two sums, computed on the canonical Hilbert bases of `F` and `E`. -/
theorem IsHilbertSchmidt.hsNormSq_adjoint {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    hsNormSq (ContinuousLinearMap.adjoint T) = hsNormSq T := by
  have hadj := hT.adjoint
  have e : ∑' i, ENNReal.ofReal (‖T (hsBasis 𝕜 E i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖(ContinuousLinearMap.adjoint T) (hsBasis 𝕜 F j)‖ ^ 2) :=
    hsE_eq_adjoint (hsBasis 𝕜 E) (hsBasis 𝕜 F) T
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hT,
    ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hadj] at e
  have hval := congrArg ENNReal.toReal e
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hval
  rw [hsNormSq_eq hadj (hsBasis 𝕜 F)]
  exact hval.symm

omit [CompleteSpace F] in
/-- The zero operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : E →L[𝕜] F) := by
  show Summable (fun i => ‖(0 : E →L[𝕜] F) (hsBasis 𝕜 E i)‖ ^ 2)
  simp

omit [CompleteSpace F] in
/-- Hilbert–Schmidt operators are closed under scalar multiplication:
`‖(c • T) eᵢ‖² = ‖c‖²·‖T eᵢ‖²` is summable. -/
theorem IsHilbertSchmidt.smul {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (c : 𝕜) :
    IsHilbertSchmidt (c • T) := by
  show Summable (fun i => ‖(c • T) (hsBasis 𝕜 E i)‖ ^ 2)
  refine (hT.mul_left (‖c‖ ^ 2)).congr (fun i => ?_)
  simp only [smul_apply, norm_smul]; ring

omit [CompleteSpace F] in
/-- Hilbert–Schmidt operators are closed under addition, via `‖(S + T) x‖² ≤ 2‖S x‖² + 2‖T x‖²`. -/
theorem IsHilbertSchmidt.add {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := by
  show Summable (fun i => ‖(S + T) (hsBasis 𝕜 E i)‖ ^ 2)
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((hS.mul_left 2).add (hT.mul_left 2))
  have htri : ‖(S + T) (hsBasis 𝕜 E i)‖ ≤ ‖S (hsBasis 𝕜 E i)‖ + ‖T (hsBasis 𝕜 E i)‖ := by
    simpa [add_apply] using norm_add_le (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))
  have h2 : ‖(S + T) (hsBasis 𝕜 E i)‖ ^ 2
      ≤ (‖S (hsBasis 𝕜 E i)‖ + ‖T (hsBasis 𝕜 E i)‖) ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) htri
  nlinarith [sq_nonneg (‖S (hsBasis 𝕜 E i)‖ - ‖T (hsBasis 𝕜 E i)‖), h2]

omit [CompleteSpace F] in
/-- Hilbert–Schmidt operators are closed under negation. -/
theorem IsHilbertSchmidt.neg {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (-T) := by
  have h := hT.smul (-1 : 𝕜); rwa [neg_one_smul] at h

omit [CompleteSpace F] in
/-- Hilbert–Schmidt operators are closed under subtraction. -/
theorem IsHilbertSchmidt.sub {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S - T) := by
  rw [sub_eq_add_neg]; exact hS.add hT.neg

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Left ideal property.**  Composing a Hilbert–Schmidt `T` on the left with any bounded operator
`A` stays Hilbert–Schmidt: `‖A (T eᵢ)‖² ≤ ‖A‖²·‖T eᵢ‖²`. -/
theorem IsHilbertSchmidt.comp_left {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (A : F →L[𝕜] G) :
    IsHilbertSchmidt (A ∘L T) := by
  show Summable (fun i => ‖(A ∘L T) (hsBasis 𝕜 E i)‖ ^ 2)
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hT.mul_left (‖A‖ ^ 2))
  calc ‖(A ∘L T) (hsBasis 𝕜 E i)‖ ^ 2 = ‖A (T (hsBasis 𝕜 E i))‖ ^ 2 := by rw [comp_apply]
    _ ≤ (‖A‖ * ‖T (hsBasis 𝕜 E i)‖) ^ 2 := by gcongr; exact A.le_opNorm _
    _ = ‖A‖ ^ 2 * ‖T (hsBasis 𝕜 E i)‖ ^ 2 := by ring

/-- **Right ideal property.**  Composing a Hilbert–Schmidt `T` on the right with any bounded operator
`B` stays Hilbert–Schmidt: pass to adjoints, where it becomes a left composition `B† ∘L T†` of the
Hilbert–Schmidt `T†`, then return by the double adjoint. -/
theorem IsHilbertSchmidt.comp_right {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (B : G →L[𝕜] E) :
    IsHilbertSchmidt (T ∘L B) := by
  have h1 : IsHilbertSchmidt (ContinuousLinearMap.adjoint B ∘L ContinuousLinearMap.adjoint T) := hT.adjoint.comp_left (ContinuousLinearMap.adjoint B)
  rw [← adjoint_comp] at h1
  simpa [adjoint_adjoint] using h1.adjoint

/-- **The Hilbert–Schmidt inner product** `⟨S, T⟩_HS = ∑ᵢ ⟨S eᵢ, T eᵢ⟩`, evaluated on the canonical
Hilbert basis; convergent for Hilbert–Schmidt `S, T` (`IsHilbertSchmidt.summable_inner`). -/
noncomputable def hsInner (S T : E →L[𝕜] F) : 𝕜 :=
  ∑' i, inner 𝕜 (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))

/-- **The Hilbert–Schmidt inner product converges.**  For Hilbert–Schmidt `S, T` the entrywise inner
products are absolutely summable, `‖⟨S (b i), T (b i)⟩‖ ≤ ½(‖S (b i)‖² + ‖T (b i)‖²)`. -/
theorem IsHilbertSchmidt.summable_inner {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    Summable (fun i => inner 𝕜 (S (b i)) (T (b i))) := by
  apply Summable.of_norm_bounded (g := fun i => (‖S (b i)‖ ^ 2 + ‖T (b i)‖ ^ 2) / 2)
  · exact (((hS.summable b).add (hT.summable b)).div_const 2)
  · intro i
    calc ‖(inner 𝕜 (S (b i)) (T (b i)))‖ ≤ ‖S (b i)‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
      _ ≤ (‖S (b i)‖ ^ 2 + ‖T (b i)‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖S (b i)‖ - ‖T (b i)‖), norm_nonneg (S (b i)), norm_nonneg (T (b i))]

/-- **The Hilbert–Schmidt inner product is a squared norm on the diagonal.**
`Re⟨T, T⟩_HS = ‖T‖²_HS` — pushing `Re` through the convergent diagonal sum turns each
`⟨T eᵢ, T eᵢ⟩` into `‖T eᵢ‖²`. -/
theorem hsInner_self_re {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    RCLike.re (hsInner T T) = hsNormSq T := by
  have hsum : Summable (fun i => inner 𝕜 (T (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))) :=
    hT.summable_inner hT (hsBasis 𝕜 E)
  have hre : RCLike.re (hsInner T T)
      = ∑' i, RCLike.re (inner 𝕜 (T (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))) :=
    RCLike.reCLM.map_tsum hsum
  rw [hre]
  exact tsum_congr fun i => inner_self_eq_norm_sq _

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A real sequence with summable squares is a member of `ℓ²`. -/
theorem memℓp_two_of_sq {ι : Type*} {a : ι → ℝ} (ha : Summable (fun i => a i ^ 2)) :
    Memℓp a 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  refine ha.congr fun i => ?_
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs, sq_abs]

/-- **Cauchy–Schwarz for real series.**  `∑ᵢ aᵢ·cᵢ ≤ √(∑ᵢ aᵢ²)·√(∑ᵢ cᵢ²)` for square-summable real
sequences — the `ℓ²(ι, ℝ)` inner-product bound read through the coordinate sums. -/
theorem tsum_mul_le_sqrt_mul_sqrt {ι : Type*} {a c : ι → ℝ}
    (ha : Summable (fun i => a i ^ 2)) (hc : Summable (fun i => c i ^ 2)) :
    ∑' i, a i * c i ≤ Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, c i ^ 2) := by
  set A : lp (fun _ : ι => ℝ) 2 := ⟨a, memℓp_two_of_sq ha⟩ with hA
  set C : lp (fun _ : ι => ℝ) 2 := ⟨c, memℓp_two_of_sq hc⟩ with hC
  have hinner : inner ℝ A C = ∑' i, a i * c i := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    simp [RCLike.inner_apply]
    exact mul_comm _ _
  have hnA : ‖A‖ ^ 2 = ∑' i, a i ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) A
    simp only [ENNReal.toReal_ofNat] at h
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
    simp only [Real.rpow_natCast] at h
    rw [h]
    exact tsum_congr fun i => by rw [Real.norm_eq_abs, sq_abs]
  have hnC : ‖C‖ ^ 2 = ∑' i, c i ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) C
    simp only [ENNReal.toReal_ofNat] at h
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
    simp only [Real.rpow_natCast] at h
    rw [h]
    exact tsum_congr fun i => by rw [Real.norm_eq_abs, sq_abs]
  calc ∑' i, a i * c i = inner ℝ A C := hinner.symm
    _ ≤ ‖A‖ * ‖C‖ := real_inner_le_norm A C
    _ = Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, c i ^ 2) := by
        rw [← hnA, ← hnC, Real.sqrt_sq (norm_nonneg A), Real.sqrt_sq (norm_nonneg C)]

/-- **Polarization for the Hilbert–Schmidt pairing.**  Over any Hilbert basis `b` of `E`, the sum
`∑ᵢ ⟨S (b i), T (b i)⟩` of a Hilbert–Schmidt pair is the polarization combination of the four
basis-independent Hilbert–Schmidt norms `‖S ± T‖²_HS` and `‖S ∓ i·T‖²_HS`; in particular the value
of the sum does not depend on the basis. -/
theorem tsum_inner_basis_polarization {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    ∑' i, inner 𝕜 (S (b i)) (T (b i))
      = ((hsNormSq (S + T) : 𝕜) - (hsNormSq (S - T) : 𝕜) +
          ((hsNormSq (S - (RCLike.I : 𝕜) • T) : 𝕜) - (hsNormSq (S + (RCLike.I : 𝕜) • T) : 𝕜))
            * RCLike.I) / 4 := by
  have h1 : IsHilbertSchmidt (S + T) := hS.add hT
  have h2 : IsHilbertSchmidt (S - T) := hS.sub hT
  have h3 : IsHilbertSchmidt (S - (RCLike.I : 𝕜) • T) := hS.sub (hT.smul _)
  have h4 : IsHilbertSchmidt (S + (RCLike.I : 𝕜) • T) := hS.add (hT.smul _)
  set f₁ : ι → 𝕜 := fun i => ((‖(S + T) (b i)‖ ^ 2 : ℝ) : 𝕜) with hf₁
  set f₂ : ι → 𝕜 := fun i => ((‖(S - T) (b i)‖ ^ 2 : ℝ) : 𝕜) with hf₂
  set f₃ : ι → 𝕜 := fun i => ((‖(S - (RCLike.I : 𝕜) • T) (b i)‖ ^ 2 : ℝ) : 𝕜) with hf₃
  set f₄ : ι → 𝕜 := fun i => ((‖(S + (RCLike.I : 𝕜) • T) (b i)‖ ^ 2 : ℝ) : 𝕜) with hf₄
  have hs₁ : Summable f₁ := (RCLike.summable_ofReal (𝕜 := 𝕜)).mpr (h1.summable b)
  have hs₂ : Summable f₂ := (RCLike.summable_ofReal (𝕜 := 𝕜)).mpr (h2.summable b)
  have hs₃ : Summable f₃ := (RCLike.summable_ofReal (𝕜 := 𝕜)).mpr (h3.summable b)
  have hs₄ : Summable f₄ := (RCLike.summable_ofReal (𝕜 := 𝕜)).mpr (h4.summable b)
  have hpt : ∀ i, inner 𝕜 (S (b i)) (T (b i))
      = (f₁ i - f₂ i + (f₃ i - f₄ i) * RCLike.I) / 4 := by
    intro i
    simp only [hf₁, hf₂, hf₃, hf₄, add_apply, sub_apply, smul_apply]
    push_cast
    exact inner_eq_sum_norm_sq_div_four _ _
  have hv₁ : ∑' i, f₁ i = ((hsNormSq (S + T) : ℝ) : 𝕜) := by
    simp only [hf₁]
    rw [← RCLike.ofReal_tsum (𝕜 := 𝕜), ← hsNormSq_eq h1 b]
  have hv₂ : ∑' i, f₂ i = ((hsNormSq (S - T) : ℝ) : 𝕜) := by
    simp only [hf₂]
    rw [← RCLike.ofReal_tsum (𝕜 := 𝕜), ← hsNormSq_eq h2 b]
  have hv₃ : ∑' i, f₃ i = ((hsNormSq (S - (RCLike.I : 𝕜) • T) : ℝ) : 𝕜) := by
    simp only [hf₃]
    rw [← RCLike.ofReal_tsum (𝕜 := 𝕜), ← hsNormSq_eq h3 b]
  have hv₄ : ∑' i, f₄ i = ((hsNormSq (S + (RCLike.I : 𝕜) • T) : ℝ) : 𝕜) := by
    simp only [hf₄]
    rw [← RCLike.ofReal_tsum (𝕜 := 𝕜), ← hsNormSq_eq h4 b]
  calc ∑' i, inner 𝕜 (S (b i)) (T (b i))
      = ∑' i, ((f₁ i - f₂ i + (f₃ i - f₄ i) * RCLike.I) / 4) := tsum_congr hpt
    _ = (∑' i, (f₁ i - f₂ i + (f₃ i - f₄ i) * RCLike.I)) / 4 := tsum_div_const
    _ = ((∑' i, (f₁ i - f₂ i)) + ∑' i, (f₃ i - f₄ i) * RCLike.I) / 4 := by
        rw [(hs₁.sub hs₂).tsum_add ((hs₃.sub hs₄).mul_right _)]
    _ = ((∑' i, f₁ i) - (∑' i, f₂ i) + ((∑' i, (f₃ i - f₄ i)) * RCLike.I)) / 4 := by
        rw [hs₁.tsum_sub hs₂, tsum_mul_right]
    _ = ((∑' i, f₁ i) - (∑' i, f₂ i) + ((∑' i, f₃ i) - (∑' i, f₄ i)) * RCLike.I) / 4 := by
        rw [hs₃.tsum_sub hs₄]
    _ = ((hsNormSq (S + T) : 𝕜) - (hsNormSq (S - T) : 𝕜) +
          ((hsNormSq (S - (RCLike.I : 𝕜) • T) : 𝕜) - (hsNormSq (S + (RCLike.I : 𝕜) • T) : 𝕜))
            * RCLike.I) / 4 := by
        rw [hv₁, hv₂, hv₃, hv₄]

/-- **Basis independence of the Hilbert–Schmidt inner product.**  For Hilbert–Schmidt `S, T`, the
pairing `∑ᵢ ⟨S (b i), T (b i)⟩` has the same value over every Hilbert basis `b` of `E`, namely
`hsInner S T`: both sides are the same polarization combination of basis-independent
Hilbert–Schmidt norms. -/
theorem hsInner_eq_tsum_basis {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    hsInner S T = ∑' i, inner 𝕜 (S (b i)) (T (b i)) := by
  show ∑' i, inner 𝕜 (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i)) = _
  exact (tsum_inner_basis_polarization hS hT (hsBasis 𝕜 E)).trans
    (tsum_inner_basis_polarization hS hT b).symm

omit [CompleteSpace F] in
/-- Conjugate symmetry of the Hilbert–Schmidt inner product: `⟨S, T⟩_HS = conj ⟨T, S⟩_HS`. -/
theorem hsInner_conj_symm (S T : E →L[𝕜] F) : hsInner S T = conj (hsInner T S) := by
  rw [hsInner, hsInner, RCLike.conj_tsum]
  exact tsum_congr fun i => (inner_conj_symm _ _).symm

/-- Left additivity of the Hilbert–Schmidt inner product on Hilbert–Schmidt operators. -/
theorem hsInner_add_left {S₁ S₂ T : E →L[𝕜] F} (h₁ : IsHilbertSchmidt S₁)
    (h₂ : IsHilbertSchmidt S₂) (hT : IsHilbertSchmidt T) :
    hsInner (S₁ + S₂) T = hsInner S₁ T + hsInner S₂ T := by
  rw [hsInner, hsInner, hsInner,
    ← (h₁.summable_inner hT (hsBasis 𝕜 E)).tsum_add (h₂.summable_inner hT (hsBasis 𝕜 E))]
  exact tsum_congr fun i => by rw [add_apply, inner_add_left]

/-- Right additivity of the Hilbert–Schmidt inner product on Hilbert–Schmidt operators. -/
theorem hsInner_add_right {S T₁ T₂ : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (h₁ : IsHilbertSchmidt T₁) (h₂ : IsHilbertSchmidt T₂) :
    hsInner S (T₁ + T₂) = hsInner S T₁ + hsInner S T₂ := by
  rw [hsInner, hsInner, hsInner,
    ← (hS.summable_inner h₁ (hsBasis 𝕜 E)).tsum_add (hS.summable_inner h₂ (hsBasis 𝕜 E))]
  exact tsum_congr fun i => by rw [add_apply, inner_add_right]

omit [CompleteSpace F] in
/-- Conjugate-linear left homogeneity: `⟨c • S, T⟩_HS = conj c · ⟨S, T⟩_HS`. -/
theorem hsInner_smul_left (c : 𝕜) (S T : E →L[𝕜] F) :
    hsInner (c • S) T = conj c * hsInner S T := by
  rw [hsInner, hsInner, ← tsum_mul_left]
  exact tsum_congr fun i => by rw [smul_apply, inner_smul_left]

omit [CompleteSpace F] in
/-- Linear right homogeneity: `⟨S, c • T⟩_HS = c · ⟨S, T⟩_HS`. -/
theorem hsInner_smul_right (c : 𝕜) (S T : E →L[𝕜] F) :
    hsInner S (c • T) = c * hsInner S T := by
  rw [hsInner, hsInner, ← tsum_mul_left]
  exact tsum_congr fun i => by rw [smul_apply, inner_smul_right]

omit [CompleteSpace F] in
/-- Negation preserves the squared Hilbert--Schmidt norm. -/
theorem hsNormSq_neg_eq_self (T : E →L[𝕜] F) :
    hsNormSq (-T) = hsNormSq T := by
  unfold hsNormSq
  exact tsum_congr fun i => by simp

/-- **Hilbert--Schmidt Pythagoras.**  Hilbert--Schmidt-orthogonal operators have additive
squared norm.  This is the operator-space form of the familiar orthogonal energy partition and
is independent of the Hilbert basis used to define the pairing. -/
theorem hsNormSq_add_eq_of_hsInner_eq_zero {S T : E →L[𝕜] F}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (horth : hsInner S T = 0) :
    hsNormSq (S + T) = hsNormSq S + hsNormSq T := by
  have hST := hS.add hT
  have horth' : hsInner T S = 0 := by
    calc
      hsInner T S = conj (hsInner S T) := hsInner_conj_symm T S
      _ = 0 := by rw [horth, map_zero]
  have hpair : hsInner (S + T) (S + T) = hsInner S S + hsInner T T := by
    calc
      hsInner (S + T) (S + T) =
          hsInner S (S + T) + hsInner T (S + T) :=
        hsInner_add_left hS hT hST
      _ = (hsInner S S + hsInner S T) +
          (hsInner T S + hsInner T T) := by
        rw [hsInner_add_right hS hS hT, hsInner_add_right hT hS hT]
      _ = hsInner S S + hsInner T T := by rw [horth, horth']; abel
  calc
    hsNormSq (S + T) = RCLike.re (hsInner (S + T) (S + T)) :=
      (hsInner_self_re hST).symm
    _ = RCLike.re (hsInner S S) + RCLike.re (hsInner T T) := by
      rw [hpair, map_add]
    _ = hsNormSq S + hsNormSq T := by rw [hsInner_self_re hS, hsInner_self_re hT]

/-- Hilbert--Schmidt-orthogonal operators also satisfy the exact difference Pythagorean law.
This is the form naturally consumed by commutators, whose two off-diagonal corners occur with
opposite signs. -/
theorem hsNormSq_sub_eq_add_of_hsInner_eq_zero {S T : E →L[𝕜] F}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T)
    (horth : hsInner S T = 0) :
    hsNormSq (S - T) = hsNormSq S + hsNormSq T := by
  have horthNeg : hsInner S (-T) = 0 := by
    calc
      hsInner S (-T) = hsInner S ((-1 : 𝕜) • T) := by rw [neg_one_smul]
      _ = (-1 : 𝕜) * hsInner S T := hsInner_smul_right (-1) S T
      _ = 0 := by rw [horth, mul_zero]
  have h := hsNormSq_add_eq_of_hsInner_eq_zero hS hT.neg horthNeg
  simpa only [sub_eq_add_neg, hsNormSq_neg_eq_self] using h

omit [CompleteSpace F] in
/-- **Positive-definiteness of the Hilbert–Schmidt norm.**  `‖T‖²_HS = 0 ↔ T = 0`: each term
`‖T eᵢ‖²` of the vanishing nonnegative sum vanishes, so `T` kills a Hilbert basis and hence its
dense span.  Together with `hsInner_self_re`, the sesquilinearity, and the conjugate symmetry, this
makes `hsInner` a genuine inner product on the Hilbert–Schmidt operators. -/
theorem hsNormSq_eq_zero_iff {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    hsNormSq T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hsummable : Summable (fun i => ‖T (hsBasis 𝕜 E i)‖ ^ 2) := hT
    have hb : ∀ i, T (hsBasis 𝕜 E i) = 0 := by
      intro i
      have hle := hsummable.le_tsum i fun j _ => by positivity
      rw [show ∑' j, ‖T (hsBasis 𝕜 E j)‖ ^ 2 = hsNormSq T from rfl, h] at hle
      have hz : ‖T (hsBasis 𝕜 E i)‖ ^ 2 = 0 := le_antisymm hle (by positivity)
      simpa [pow_eq_zero_iff] using hz
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr (hsBasis 𝕜 E).dense_span) ?_
    rintro x ⟨i, rfl⟩
    simp [hb i]
  · rintro rfl
    rw [hsNormSq]
    simp

omit [CompleteSpace F] in
/-- Positive-definiteness of the Hilbert–Schmidt norm, in square-root form. -/
theorem hsNorm_eq_zero_iff {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    hsNorm T = 0 ↔ T = 0 := by
  rw [hsNorm, Real.sqrt_eq_zero (hsNormSq_nonneg T)]
  exact hsNormSq_eq_zero_iff hT

omit [CompleteSpace F] in
/-- **Cauchy–Schwarz for the Hilbert–Schmidt inner product.**
`‖⟨S, T⟩_HS‖ ≤ ‖S‖_HS · ‖T‖_HS`. -/
theorem norm_hsInner_le {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    ‖hsInner S T‖ ≤ hsNorm S * hsNorm T := by
  have hcross : Summable (fun i => ‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hS.mul_left (2⁻¹)).add (hT.mul_left (2⁻¹)))
    nlinarith [sq_nonneg (‖S (hsBasis 𝕜 E i)‖ - ‖T (hsBasis 𝕜 E i)‖),
      norm_nonneg (S (hsBasis 𝕜 E i)), norm_nonneg (T (hsBasis 𝕜 E i))]
  have hnorm_sum : Summable (fun i => ‖inner 𝕜 (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_inner_le_norm _ _) hcross
  calc ‖hsInner S T‖
      ≤ ∑' i, ‖inner 𝕜 (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))‖ := by
        rw [hsInner]
        exact norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' i, ‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖ :=
        Summable.tsum_le_tsum (fun i => norm_inner_le_norm _ _) hnorm_sum hcross
    _ ≤ Real.sqrt (∑' i, ‖S (hsBasis 𝕜 E i)‖ ^ 2) * Real.sqrt (∑' i, ‖T (hsBasis 𝕜 E i)‖ ^ 2) :=
        tsum_mul_le_sqrt_mul_sqrt hS hT
    _ = hsNorm S * hsNorm T := rfl

omit [CompleteSpace F] in
/-- **Triangle inequality for the Hilbert–Schmidt norm.**  `‖S + T‖_HS ≤ ‖S‖_HS + ‖T‖_HS`:
Minkowski for the square-summable norm sequences, via the series Cauchy–Schwarz bound on the cross
term.  With `hsNorm_eq_zero_iff` and the homogeneity from `IsHilbertSchmidt.smul`, the
Hilbert–Schmidt operators carry a genuine norm. -/
theorem hsNorm_add_le {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNorm (S + T) ≤ hsNorm S + hsNorm T := by
  have hcross : Summable (fun i => ‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hS.mul_left (2⁻¹)).add (hT.mul_left (2⁻¹)))
    nlinarith [sq_nonneg (‖S (hsBasis 𝕜 E i)‖ - ‖T (hsBasis 𝕜 E i)‖),
      norm_nonneg (S (hsBasis 𝕜 E i)), norm_nonneg (T (hsBasis 𝕜 E i))]
  have hcs : ∑' i, ‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖ ≤ hsNorm S * hsNorm T :=
    tsum_mul_le_sqrt_mul_sqrt hS hT
  have hSsum : Summable (fun i => ‖S (hsBasis 𝕜 E i)‖ ^ 2) := hS
  have hTsum : Summable (fun i => ‖T (hsBasis 𝕜 E i)‖ ^ 2) := hT
  have key : hsNormSq (S + T) ≤ (hsNorm S + hsNorm T) ^ 2 := by
    have hbound : Summable (fun i =>
        ‖S (hsBasis 𝕜 E i)‖ ^ 2 + 2 * (‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖)
          + ‖T (hsBasis 𝕜 E i)‖ ^ 2) :=
      (hSsum.add ((hcross.mul_left 2).add hTsum)).congr fun i => by ring
    have hle : hsNormSq (S + T)
        ≤ ∑' i, (‖S (hsBasis 𝕜 E i)‖ ^ 2 + 2 * (‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖)
            + ‖T (hsBasis 𝕜 E i)‖ ^ 2) := by
      refine Summable.tsum_le_tsum (fun i => ?_) (hS.add hT) hbound
      have htri : ‖(S + T) (hsBasis 𝕜 E i)‖ ≤ ‖S (hsBasis 𝕜 E i)‖ + ‖T (hsBasis 𝕜 E i)‖ := by
        simpa [add_apply] using norm_add_le (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))
      nlinarith [norm_nonneg ((S + T) (hsBasis 𝕜 E i)), norm_nonneg (S (hsBasis 𝕜 E i)),
        norm_nonneg (T (hsBasis 𝕜 E i))]
    have hsplit : ∑' i, (‖S (hsBasis 𝕜 E i)‖ ^ 2
          + 2 * (‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖) + ‖T (hsBasis 𝕜 E i)‖ ^ 2)
        = hsNormSq S + 2 * (∑' i, ‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖) + hsNormSq T := by
      rw [(hSsum.add (hcross.mul_left 2)).tsum_add hTsum, hSsum.tsum_add (hcross.mul_left 2),
        tsum_mul_left]
      rfl
    have hsq : hsNormSq S = hsNorm S ^ 2 := by
      rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg S)]
    have htq : hsNormSq T = hsNorm T ^ 2 := by
      rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg T)]
    have hle2 : hsNormSq (S + T)
        ≤ hsNormSq S + 2 * (∑' i, ‖S (hsBasis 𝕜 E i)‖ * ‖T (hsBasis 𝕜 E i)‖) + hsNormSq T :=
      hle.trans_eq hsplit
    nlinarith [hcs, hsNorm_nonneg S, hsNorm_nonneg T]
  calc hsNorm (S + T) = Real.sqrt (hsNormSq (S + T)) := rfl
    _ ≤ Real.sqrt ((hsNorm S + hsNorm T) ^ 2) := Real.sqrt_le_sqrt key
    _ = hsNorm S + hsNorm T := by
        rw [Real.sqrt_sq (add_nonneg (hsNorm_nonneg S) (hsNorm_nonneg T))]

/-- **The adjoint reverses the Hilbert–Schmidt inner product.**  `⟨S†, T†⟩_HS = ⟨T, S⟩_HS`: the
polarization combination for the adjoint pair collapses onto the conjugated combination for
`S, T`, because the adjoint preserves each Hilbert–Schmidt norm while conjugating the scalar `i`. -/
theorem hsInner_adjoint_adjoint {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) :
    hsInner (ContinuousLinearMap.adjoint S) (ContinuousLinearMap.adjoint T) = hsInner T S := by
  have h1 : IsHilbertSchmidt (S + T) := hS.add hT
  have h2 : IsHilbertSchmidt (S - T) := hS.sub hT
  have h3 : IsHilbertSchmidt (S - (RCLike.I : 𝕜) • T) := hS.sub (hT.smul _)
  have h4 : IsHilbertSchmidt (S + (RCLike.I : 𝕜) • T) := hS.add (hT.smul _)
  have e1 : ContinuousLinearMap.adjoint S + ContinuousLinearMap.adjoint T
      = ContinuousLinearMap.adjoint (S + T) := (map_add ContinuousLinearMap.adjoint S T).symm
  have e2 : ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T
      = ContinuousLinearMap.adjoint (S - T) := (map_sub ContinuousLinearMap.adjoint S T).symm
  have e3 : ContinuousLinearMap.adjoint S
        - (RCLike.I : 𝕜) • ContinuousLinearMap.adjoint T
      = ContinuousLinearMap.adjoint (S + (RCLike.I : 𝕜) • T) := by
    rw [map_add, ContinuousLinearMap.adjoint.map_smulₛₗ, RCLike.conj_I, neg_smul,
      ← sub_eq_add_neg]
  have e4 : ContinuousLinearMap.adjoint S
        + (RCLike.I : 𝕜) • ContinuousLinearMap.adjoint T
      = ContinuousLinearMap.adjoint (S - (RCLike.I : 𝕜) • T) := by
    rw [map_sub, ContinuousLinearMap.adjoint.map_smulₛₗ, RCLike.conj_I, neg_smul,
      sub_neg_eq_add]
  have hL' : hsInner (ContinuousLinearMap.adjoint S) (ContinuousLinearMap.adjoint T)
      = ((hsNormSq (S + T) : 𝕜) - (hsNormSq (S - T) : 𝕜) +
          ((hsNormSq (S + (RCLike.I : 𝕜) • T) : 𝕜) - (hsNormSq (S - (RCLike.I : 𝕜) • T) : 𝕜))
            * RCLike.I) / 4 := by
    have hL := tsum_inner_basis_polarization hS.adjoint hT.adjoint (hsBasis 𝕜 F)
    rw [e1, e2, e3, e4, h1.hsNormSq_adjoint, h2.hsNormSq_adjoint, h4.hsNormSq_adjoint,
      h3.hsNormSq_adjoint] at hL
    exact hL
  have hR' : hsInner S T
      = ((hsNormSq (S + T) : 𝕜) - (hsNormSq (S - T) : 𝕜) +
          ((hsNormSq (S - (RCLike.I : 𝕜) • T) : 𝕜) - (hsNormSq (S + (RCLike.I : 𝕜) • T) : 𝕜))
            * RCLike.I) / 4 :=
    tsum_inner_basis_polarization hS hT (hsBasis 𝕜 E)
  rw [hL', show hsInner T S = conj (hsInner S T) from hsInner_conj_symm T S, hR']
  simp only [map_div₀, map_add, map_sub, map_mul, map_ofNat, RCLike.conj_ofReal, RCLike.conj_I]
  ring

end ContinuousLinearMap
