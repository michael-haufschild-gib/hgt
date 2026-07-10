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
* `ContinuousLinearMap.IsHilbertSchmidt` — the Hilbert–Schmidt predicate.
* `ContinuousLinearMap.hsE_eq_adjoint` — the master `ℝ≥0∞` basis/adjoint identity.
* `IsHilbertSchmidt.summable` — square-summability holds over *every* Hilbert basis once it holds over
  one: the definition does not depend on the choice of basis.
* `IsHilbertSchmidt.tsum_normSq_eq`, `hsNormSq`, `hsNorm`, `hsNormSq_eq` — the basis-independent
  Hilbert–Schmidt norm.
* `IsHilbertSchmidt.adjoint`, `IsHilbertSchmidt.hsNormSq_adjoint` — the adjoint is Hilbert–Schmidt with
  the same Hilbert–Schmidt norm.
* `isHilbertSchmidt_zero`, `IsHilbertSchmidt.add`, `IsHilbertSchmidt.smul`, `IsHilbertSchmidt.neg`,
  `IsHilbertSchmidt.sub` — the Hilbert–Schmidt operators form a submodule of `E →L[𝕜] F`.
* `IsHilbertSchmidt.comp_left`, `IsHilbertSchmidt.comp_right` — the two-sided ideal property: composing
  a Hilbert–Schmidt operator with any bounded operator stays Hilbert–Schmidt.
* `ContinuousLinearMap.hsInner`, `IsHilbertSchmidt.summable_inner`, `hsInner_self_re` — the
  Hilbert–Schmidt inner product `⟨S, T⟩_HS = ∑ᵢ ⟨S eᵢ, T eᵢ⟩`, convergent for Hilbert–Schmidt `S, T`,
  with `Re⟨T, T⟩_HS = ‖T‖²_HS`.
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

/-- A continuous linear map `T : E →L[𝕜] F` is **Hilbert–Schmidt** when the squared norms of its
values on some Hilbert basis of `E` are summable, `∑ᵢ ‖T (b i)‖² < ∞`.  `IsHilbertSchmidt.summable`
shows the choice of basis is immaterial. -/
def IsHilbertSchmidt (T : E →L[𝕜] F) : Prop :=
  ∃ (ι : Type*) (b : HilbertBasis ι 𝕜 E), Summable (fun i => ‖T (b i)‖ ^ 2)

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
      = ∑' j, ENNReal.ofReal (‖(adjoint T) (c j)‖ ^ 2) := by
  have row : ∀ i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := by
    intro i
    rw [← c.tsum_norm_inner_sq (T (b i)),
      ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (c.summable_norm_inner_sq (T (b i)))]
  have col : ∀ j, ENNReal.ofReal (‖(adjoint T) (c j)‖ ^ 2)
      = ∑' i, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := by
    intro j
    rw [← b.tsum_norm_inner_sq ((adjoint T) (c j)),
      ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
        (b.summable_norm_inner_sq ((adjoint T) (c j)))]
    refine tsum_congr fun i => ?_
    have hnorm : ‖inner 𝕜 (b i) ((adjoint T) (c j))‖ = ‖inner 𝕜 (c j) (T (b i))‖ := by
      calc ‖inner 𝕜 (b i) ((adjoint T) (c j))‖
          = ‖inner 𝕜 ((adjoint T) (c j)) (b i)‖ := by
            rw [← inner_conj_symm ((adjoint T) (c j)) (b i), RCLike.norm_conj]
        _ = ‖inner 𝕜 (c j) (T (b i))‖ := by rw [adjoint_inner_left]
    rw [hnorm]
  calc ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := tsum_congr row
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner 𝕜 (c j) (T (b i))‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ENNReal.ofReal (‖(adjoint T) (c j)‖ ^ 2) := (tsum_congr col).symm

/-- **Basis-independence of Hilbert–Schmidt summability.**  If `T` is Hilbert–Schmidt then
`i ↦ ‖T (b i)‖²` is summable for *every* Hilbert basis `b` of `E`, not merely the witnessing one:
route the finiteness through a fixed Hilbert basis of `F` with the master identity. -/
theorem IsHilbertSchmidt.summable {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) : Summable (fun i => ‖T (b i)‖ ^ 2) := by
  obtain ⟨_, b₀, hb₀⟩ := hT
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  refine summable_of_ofReal_tsum_ne_top (fun i => by positivity) ?_
  rw [hsE_eq_adjoint b c T, ← hsE_eq_adjoint b₀ c T]
  exact ofReal_tsum_ne_top (fun i => by positivity) hb₀

/-- Hilbert–Schmidt is equivalent to square-summability over any prescribed Hilbert basis. -/
theorem isHilbertSchmidt_iff_summable {T : E →L[𝕜] F} {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    IsHilbertSchmidt T ↔ Summable (fun i => ‖T (b i)‖ ^ 2) :=
  ⟨fun hT => hT.summable b, fun hb => ⟨ι, b, hb⟩⟩

/-- **Basis-independence of the Hilbert–Schmidt norm.**  For a Hilbert–Schmidt `T`, the value
`∑ᵢ ‖T (b i)‖²` is the same for every Hilbert basis `b`: both equal the adjoint sum over a common
Hilbert basis of `F` (master identity), and `ENNReal.ofReal` is injective on the nonnegatives. -/
theorem IsHilbertSchmidt.tsum_normSq_eq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι κ : Type*} (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis κ 𝕜 E) :
    ∑' i, ‖T (b i)‖ ^ 2 = ∑' i', ‖T (b' i')‖ ^ 2 := by
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  have e : ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2) = ∑' i', ENNReal.ofReal (‖T (b' i')‖ ^ 2) :=
    (hsE_eq_adjoint b c T).trans (hsE_eq_adjoint b' c T).symm
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (hT.summable b),
    ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (hT.summable b')] at e
  have := congrArg ENNReal.toReal e
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at this

/-- A canonical Hilbert basis of `E`, chosen from `exists_hilbertBasis`, indexing the definition of the
Hilbert–Schmidt norm. -/
noncomputable def hsBasis (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : HilbertBasis (exists_hilbertBasis 𝕜 E).choose 𝕜 E :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose

/-- The **Hilbert–Schmidt norm squared** `‖T‖²_HS = ∑ᵢ ‖T eᵢ‖²`, evaluated on the canonical Hilbert
basis; `hsNormSq_eq` shows it is the same sum for every Hilbert basis. -/
noncomputable def hsNormSq (T : E →L[𝕜] F) : ℝ := ∑' i, ‖T (hsBasis 𝕜 E i)‖ ^ 2

/-- The **Hilbert–Schmidt norm** `‖T‖_HS = √(∑ᵢ ‖T eᵢ‖²)`. -/
noncomputable def hsNorm (T : E →L[𝕜] F) : ℝ := Real.sqrt (hsNormSq T)

theorem hsNormSq_nonneg (T : E →L[𝕜] F) : 0 ≤ hsNormSq T := tsum_nonneg fun _ => by positivity

theorem hsNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ hsNorm T := Real.sqrt_nonneg _

/-- The Hilbert–Schmidt norm squared is computed by any Hilbert basis: `‖T‖²_HS = ∑ᵢ ‖T (b i)‖²`. -/
theorem hsNormSq_eq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    hsNormSq T = ∑' i, ‖T (b i)‖ ^ 2 :=
  hT.tsum_normSq_eq (hsBasis 𝕜 E) b

/-- **The adjoint of a Hilbert–Schmidt operator is Hilbert–Schmidt.**  The master identity carries the
finite sum `∑ᵢ ‖T (b i)‖²` to `∑ⱼ ‖T† (c j)‖²` for a Hilbert basis `c` of `F`, which is then summable. -/
theorem IsHilbertSchmidt.adjoint {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (adjoint T) := by
  obtain ⟨_, b, hb⟩ := hT
  obtain ⟨wc, c, -⟩ := exists_hilbertBasis 𝕜 F
  refine ⟨wc, c, summable_of_ofReal_tsum_ne_top (fun j => by positivity) ?_⟩
  rw [← hsE_eq_adjoint b c T]
  exact ofReal_tsum_ne_top (fun i => by positivity) hb

/-- **The adjoint preserves the Hilbert–Schmidt norm.**  `‖T†‖²_HS = ‖T‖²_HS`: the master identity
equates the two sums, computed on the canonical Hilbert bases of `F` and `E`. -/
theorem IsHilbertSchmidt.hsNormSq_adjoint {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    hsNormSq (adjoint T) = hsNormSq T := by
  obtain ⟨wc, c, -⟩ := exists_hilbertBasis 𝕜 F
  have hadj := hT.adjoint
  have e : ∑' i, ENNReal.ofReal (‖T (hsBasis 𝕜 E i)‖ ^ 2)
      = ∑' j, ENNReal.ofReal (‖(adjoint T) (c j)‖ ^ 2) := hsE_eq_adjoint (hsBasis 𝕜 E) c T
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (hT.summable (hsBasis 𝕜 E)),
    ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (hadj.summable c)] at e
  have hval := congrArg ENNReal.toReal e
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hval
  rw [hsNormSq_eq hadj c, ← hval]
  rfl

/-- The zero operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : E →L[𝕜] F) :=
  ⟨_, hsBasis 𝕜 E, by simpa using summable_zero⟩

/-- Hilbert–Schmidt operators are closed under scalar multiplication:
`‖(c • T) (b i)‖² = ‖c‖²·‖T (b i)‖²` is summable. -/
theorem IsHilbertSchmidt.smul {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (c : 𝕜) :
    IsHilbertSchmidt (c • T) := by
  refine ⟨_, hsBasis 𝕜 E, ((hT.summable (hsBasis 𝕜 E)).mul_left (‖c‖ ^ 2)).congr (fun i => ?_)⟩
  simp only [smul_apply, norm_smul]; ring

/-- Hilbert–Schmidt operators are closed under addition, via `‖(S + T) x‖² ≤ 2‖S x‖² + 2‖T x‖²`. -/
theorem IsHilbertSchmidt.add {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := by
  refine ⟨_, hsBasis 𝕜 E,
    Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (((hS.summable (hsBasis 𝕜 E)).mul_left 2).add ((hT.summable (hsBasis 𝕜 E)).mul_left 2))⟩
  have htri : ‖(S + T) (hsBasis 𝕜 E i)‖ ≤ ‖S (hsBasis 𝕜 E i)‖ + ‖T (hsBasis 𝕜 E i)‖ := by
    simpa [add_apply] using norm_add_le (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))
  have h2 : ‖(S + T) (hsBasis 𝕜 E i)‖ ^ 2
      ≤ (‖S (hsBasis 𝕜 E i)‖ + ‖T (hsBasis 𝕜 E i)‖) ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) htri
  nlinarith [sq_nonneg (‖S (hsBasis 𝕜 E i)‖ - ‖T (hsBasis 𝕜 E i)‖), h2]

/-- Hilbert–Schmidt operators are closed under negation. -/
theorem IsHilbertSchmidt.neg {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (-T) := by
  simpa using hT.smul (-1 : 𝕜)

/-- Hilbert–Schmidt operators are closed under subtraction. -/
theorem IsHilbertSchmidt.sub {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S - T) := by
  simpa [sub_eq_add_neg] using hS.add hT.neg

/-- **Left ideal property.**  Composing a Hilbert–Schmidt `T` on the left with any bounded operator
`A` stays Hilbert–Schmidt: `‖A (T (b i))‖² ≤ ‖A‖²·‖T (b i)‖²`. -/
theorem IsHilbertSchmidt.comp_left {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (A : F →L[𝕜] G) :
    IsHilbertSchmidt (A ∘L T) := by
  refine ⟨_, hsBasis 𝕜 E,
    Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hT.summable (hsBasis 𝕜 E)).mul_left (‖A‖ ^ 2))⟩
  calc ‖(A ∘L T) (hsBasis 𝕜 E i)‖ ^ 2 = ‖A (T (hsBasis 𝕜 E i))‖ ^ 2 := by rw [comp_apply]
    _ ≤ (‖A‖ * ‖T (hsBasis 𝕜 E i)‖) ^ 2 := by
        gcongr; exact A.le_opNorm _
    _ = ‖A‖ ^ 2 * ‖T (hsBasis 𝕜 E i)‖ ^ 2 := by ring

/-- **Right ideal property.**  Composing a Hilbert–Schmidt `T` on the right with any bounded operator
`B` stays Hilbert–Schmidt: pass to adjoints, where it becomes a left composition
`B† ∘L T†` of the Hilbert–Schmidt `T†`, then return by the double adjoint. -/
theorem IsHilbertSchmidt.comp_right {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (B : G →L[𝕜] E) :
    IsHilbertSchmidt (T ∘L B) := by
  have h1 : IsHilbertSchmidt (adjoint B ∘L adjoint T) := hT.adjoint.comp_left (adjoint B)
  rw [← adjoint_comp] at h1
  simpa [adjoint_adjoint] using h1.adjoint

/-- **The Hilbert–Schmidt inner product** `⟨S, T⟩_HS = ∑ᵢ ⟨S eᵢ, T eᵢ⟩`, evaluated on the canonical
Hilbert basis; convergent for Hilbert–Schmidt `S, T` (`IsHilbertSchmidt.summable_inner`). -/
noncomputable def hsInner (S T : E →L[𝕜] F) : 𝕜 :=
  ∑' i, inner 𝕜 (S (hsBasis 𝕜 E i)) (T (hsBasis 𝕜 E i))

/-- **The Hilbert–Schmidt inner product converges.**  For Hilbert–Schmidt `S, T` the entrywise
inner products are absolutely summable, `‖⟨S (b i), T (b i)⟩‖ ≤ ½(‖S (b i)‖² + ‖T (b i)‖²)`. -/
theorem IsHilbertSchmidt.summable_inner {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    Summable (fun i => inner 𝕜 (S (b i)) (T (b i))) := by
  apply Summable.of_norm_bounded
    (g := fun i => (‖S (b i)‖ ^ 2 + ‖T (b i)‖ ^ 2) / 2)
  · exact ((hS.summable b).add (hT.summable b)).div_const 2
  · intro i
    calc ‖inner 𝕜 (S (b i)) (T (b i))‖ ≤ ‖S (b i)‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
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
