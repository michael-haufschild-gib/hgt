import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.TwoPathIncompatibility

/-!
# The literal cyclic source and its unique orientation quotient

The physical landing of the two-path family has two independent input legs.  The *literal cyclic
source* is more structured: it carries an anti-diagonal cyclic boundary already.

Let `S` be an `R`-module with an involution `τ_S` and a surjective `τ_S`-invariant trace
`ε : S → R`.  The source-pointed landing is `C(x) = ε(x) e₁`, `L_src = c C`, and

`Δ_src = T_q L_src - L_src τ_S`,  `B_src = im Δ_src + im (T_q Δ_src)`,  `Q_src = U / B_src`.

The results proved here:

* `srcDefect_apply` / `srcRotDefect_apply` — `Δ_src(x) = cε(x)(-1,q)` and
  `T_qΔ_src(x) = qcε(x)(1,-1)`;
* `range_srcDefect` / `range_srcRotDefect` — the two ranges are the lines `R(-1,q)` and `R(q,-q)`;
* `srcBoundary_eq_ker_coordSum` — `B_src` is exactly the kernel of the coordinate-sum map
  `φ(x,y) = x + y mod I`;
* `srcIncompatEquiv` — hence `Q_src ≅ R/I`, one absolute orientation line;
* `annihilator_srcIncompatModule` — `Ann_R Q_src = I`;
* `wallSquare_le_srcBoundary`, `antidiagonal_ker_coordSumQuot` — the comparison
  `0 → (R/I)(1,-1) → Q = (R/I)² → Q_src = R/I → 0`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u v

section General

variable {R : Type u} [CommRing R] {S : Type v} [AddCommGroup S] [Module R S]

/-- The source-pointed landing `L_src(x) = c ε(x) e₁`. -/
def srcLanding (eps : S →ₗ[R] R) (c : R) : S →ₗ[R] (R × R) :=
  LinearMap.inl R R R ∘ₗ (c • eps)

@[simp] theorem srcLanding_apply (eps : S →ₗ[R] R) (c : R) (x : S) :
    srcLanding eps c x = (c * eps x, 0) := rfl

/-- The literal cyclic source defect `Δ_src = T_q L_src - L_src τ_S`. -/
def srcDefect (tauS : S →ₗ[R] S) (eps : S →ₗ[R] R) (q c : R) : S →ₗ[R] (R × R) :=
  paracyclicRot q ∘ₗ srcLanding eps c - srcLanding eps c ∘ₗ tauS

/-- The rotated source defect `T_q Δ_src`. -/
def srcRotDefect (tauS : S →ₗ[R] S) (eps : S →ₗ[R] R) (q c : R) : S →ₗ[R] (R × R) :=
  paracyclicRot q ∘ₗ srcDefect tauS eps q c

variable {tauS : S →ₗ[R] S} {eps : S →ₗ[R] R} {q c : R}

/-- `Δ_src(x) = cε(x)·(-1, q)` when the trace is `τ_S`-invariant. -/
theorem srcDefect_apply (hinv : ∀ x, eps (tauS x) = eps x) (x : S) :
    srcDefect tauS eps q c x = (c * eps x) • ((-1 : R), q) := by
  simp [srcDefect, hinv x, Prod.smul_def, smul_eq_mul, mul_comm]

/-- `T_qΔ_src(x) = qcε(x)·(1, -1)`. -/
theorem srcRotDefect_apply (hinv : ∀ x, eps (tauS x) = eps x) (x : S) :
    srcRotDefect tauS eps q c x = (c * eps x) • (q, -q) := by
  rw [srcRotDefect, LinearMap.comp_apply, srcDefect_apply hinv]
  simp [Prod.ext_iff, Prod.smul_def, smul_eq_mul]
  ring

/-- The minimal source boundary `B_src = im Δ_src + im (T_q Δ_src)`. -/
def srcBoundary (tauS : S →ₗ[R] S) (eps : S →ₗ[R] R) (q c : R) : Submodule R (R × R) :=
  LinearMap.range (srcDefect tauS eps q c) ⊔ LinearMap.range (srcRotDefect tauS eps q c)

/-- The source incompatibility module `Q_src = U / B_src`. -/
abbrev srcIncompatModule (tauS : S →ₗ[R] S) (eps : S →ₗ[R] R) (q c : R) : Type u :=
  (R × R) ⧸ srcBoundary tauS eps q c

/-- Under a surjective trace and a unit landing scalar, `c ε` is surjective. -/
theorem cEps_surjective (heps : Function.Surjective eps) (hc : IsUnit c) (r : R) :
    ∃ x : S, c * eps x = r := by
  obtain ⟨d, hd⟩ := hc.exists_right_inv
  obtain ⟨x, hx⟩ := heps (d * r)
  exact ⟨x, by rw [hx, ← mul_assoc, hd, one_mul]⟩

theorem range_srcDefect (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hc : IsUnit c) :
    LinearMap.range (srcDefect tauS eps q c) = Submodule.span R {((-1 : R), q)} := by
  ext p
  simp only [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨c * eps x, (srcDefect_apply hinv x).symm⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨x, hx⟩ := cEps_surjective heps hc r
    exact ⟨x, by rw [srcDefect_apply hinv, hx]⟩

theorem range_srcRotDefect (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hc : IsUnit c) :
    LinearMap.range (srcRotDefect tauS eps q c) = Submodule.span R {(q, -q)} := by
  ext p
  simp only [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨c * eps x, (srcRotDefect_apply hinv x).symm⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨x, hx⟩ := cEps_surjective heps hc r
    exact ⟨x, by rw [srcRotDefect_apply hinv, hx]⟩

/-- The coordinate-sum map `φ(x,y) = x + y mod I`, `I = (q-1)`. -/
def coordSum (q : R) : (R × R) →ₗ[R] R ⧸ Ideal.span {q - 1} :=
  (Ideal.span {q - 1} : Ideal R).mkQ ∘ₗ (LinearMap.fst R R R + LinearMap.snd R R R)

@[simp] theorem coordSum_apply (q : R) (p : R × R) :
    coordSum q p = Ideal.Quotient.mk (Ideal.span {q - 1}) (p.1 + p.2) := rfl

theorem coordSum_surjective (q : R) : Function.Surjective (coordSum q) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨(x, 0), by simp⟩

theorem mem_ker_coordSum {q : R} {p : R × R} :
    p ∈ LinearMap.ker (coordSum q) ↔ ∃ t, p.1 + p.2 = (q - 1) * t := by
  simp only [LinearMap.mem_ker, coordSum_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, dvd_def]

/-- **Theorem 4A.1, kernel identification.**  The minimal source boundary is exactly the kernel of
the coordinate-sum map: `B_src = ker φ`. -/
theorem srcBoundary_eq_ker_coordSum (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c) :
    srcBoundary tauS eps q c = LinearMap.ker (coordSum q) := by
  obtain ⟨d, hd⟩ := hq.exists_right_inv
  apply le_antisymm
  · rw [srcBoundary, sup_le_iff]
    constructor
    · rw [range_srcDefect hinv heps hc, Submodule.span_le]
      rintro p rfl
      exact mem_ker_coordSum.2 ⟨1, by ring⟩
    · rw [range_srcRotDefect hinv heps hc, Submodule.span_le]
      rintro p rfl
      exact mem_ker_coordSum.2 ⟨0, by ring⟩
  · intro p hp
    obtain ⟨t, ht⟩ := mem_ker_coordSum.1 hp
    rw [srcBoundary, range_srcDefect hinv heps hc, range_srcRotDefect hinv heps hc]
    have hqd : d * q = 1 := by rw [mul_comm]; exact hd
    have hsplit :
        p = t • ((-1 : R), q) + (d * (t + p.1)) • (q, -q) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination (-(t + p.1)) * hqd
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination (t + p.1) * hqd + ht
    rw [hsplit]
    exact Submodule.add_mem_sup
      (Submodule.mem_span_singleton.2 ⟨t, rfl⟩)
      (Submodule.mem_span_singleton.2 ⟨d * (t + p.1), rfl⟩)

/-- **Theorem 4A.1.**  The literal cyclic source leaves exactly one absolute orientation line:
`Q_src ≅ R/I`. -/
noncomputable def srcIncompatEquiv (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c) :
    srcIncompatModule tauS eps q c ≃ₗ[R] (R ⧸ Ideal.span {q - 1} : Type u) :=
  (Submodule.quotEquivOfEq _ _ (srcBoundary_eq_ker_coordSum hinv heps hq hc)).trans
    (LinearMap.quotKerEquivOfSurjective _ (coordSum_surjective q))

/-- **Theorem 4A.1, annihilator.**  `Ann_R Q_src = I`. -/
theorem annihilator_srcIncompatModule (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c) :
    Module.annihilator R (srcIncompatModule tauS eps q c) = Ideal.span {q - 1} := by
  rw [(srcIncompatEquiv hinv heps hq hc).annihilator_eq, Ideal.annihilator_quotient]

end General

section Comparison

variable {R : Type u} [CommRing R] (q : R)

/-- The wall submodule is contained in the kernel of the coordinate-sum map: the physical two-leg
boundary is smaller than the literal cyclic source boundary. -/
theorem wallSquare_le_ker_coordSum : wallSquare q ≤ LinearMap.ker (coordSum q) := by
  rintro p hp
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := mem_wallSquare.1 hp
  exact mem_ker_coordSum.2 ⟨x + y, by rw [hx, hy]; ring⟩

/-- The coordinate-sum map on the identity fibre `(R/I)² → R/I`. -/
def coordSumQuot :
    ((R ⧸ Ideal.span {q - 1} : Type u) × (R ⧸ Ideal.span {q - 1} : Type u)) →ₗ[R]
      (R ⧸ Ideal.span {q - 1} : Type u) :=
  LinearMap.fst _ _ _ + LinearMap.snd _ _ _

@[simp] theorem coordSumQuot_apply
    (p : (R ⧸ Ideal.span {q - 1} : Type u) × (R ⧸ Ideal.span {q - 1} : Type u)) :
    coordSumQuot q p = p.1 + p.2 := rfl

theorem coordSumQuot_surjective : Function.Surjective (coordSumQuot q) :=
  fun z => ⟨(z, 0), by simp⟩

/-- The anti-diagonal embedding `a ↦ (a, -a)` of the identity fibre. -/
def antidiagonal :
    (R ⧸ Ideal.span {q - 1} : Type u) →ₗ[R]
      ((R ⧸ Ideal.span {q - 1} : Type u) × (R ⧸ Ideal.span {q - 1} : Type u)) :=
  LinearMap.prod LinearMap.id (-LinearMap.id)

@[simp] theorem antidiagonal_apply (a : R ⧸ Ideal.span {q - 1}) :
    antidiagonal q a = (a, -a) := rfl

theorem antidiagonal_injective : Function.Injective (antidiagonal q) := by
  intro a b h
  simpa using congrArg Prod.fst h

/-- **Corollary 4A.2.**  On the identity fibre the coordinate-sum map is surjective with kernel the
anti-diagonal line: `0 → (R/I)(1,-1) → (R/I)² → R/I → 0`. -/
theorem ker_coordSumQuot :
    LinearMap.ker (coordSumQuot q) = LinearMap.range (antidiagonal q) := by
  ext p
  simp only [LinearMap.mem_ker, coordSumQuot_apply, LinearMap.mem_range, antidiagonal_apply]
  constructor
  · intro h
    refine ⟨p.1, Prod.ext rfl ?_⟩
    have : p.2 = -p.1 := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    exact this.symm
  · rintro ⟨a, rfl⟩
    simp

end Comparison

section Nonvacuity

variable {R : Type u} [CommRing R]

/-- The tautological literal cyclic source: `S = R` with trivial involution and identity trace.
This shows the hypotheses of Theorem 4A.1 are satisfiable. -/
theorem exists_srcData :
    ∃ (tauS : R →ₗ[R] R) (eps : R →ₗ[R] R),
      (∀ x, eps (tauS x) = eps x) ∧ Function.Surjective eps :=
  ⟨LinearMap.id, LinearMap.id, fun _ => rfl, fun x => ⟨x, rfl⟩⟩

end Nonvacuity

end GaloisForLFunctions.HTGeometry.DerivedSelection
