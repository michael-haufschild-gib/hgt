import GaloisForLFunctions.RHTower.SymplecticMultiplicity

/-!
# The cyclic obstruction: symplectic self-adjointness excludes single-channel carriers

For an endomorphism `K` with a cyclic vector, every `K`-invariant bilinear form is symmetric:
on iterates, `B (K^i v) (K^j v) = B v (K^{i+j} v)` depends only on `i + j`.  Hence an
alternating invariant form on a cyclic module vanishes, and a symplectic structure
(nondegenerate alternating, `K` self-adjoint) forces the carrier to be non-cyclic — the module
must have at least two channels.

Applied through the restriction machinery: for a symplectically self-adjoint endomorphism,
**no nontrivial generalized eigenspace admits a cyclic vector**.  This strengthens the even-
multiplicity mechanism: not only is every algebraic multiplicity even, no root space is a
single Jordan block — the local divisor decomposes into at least two Jordan channels at every
eigenvalue.  In particular the canonical single-zero divisor model (multiplication on a cyclic
jet algebra) can never carry the symplectic symmetry; any carrier realizing it must contain a
second channel that the cyclic analytic model does not supply.
-/

open Module

namespace RHTower

section Cyclic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A cyclic vector for an endomorphism: the iterates span the whole space. -/
def CyclicVector (K : Module.End ℂ V) (v : V) : Prop :=
  Submodule.span ℂ (Set.range fun n : ℕ => (K ^ n) v) = ⊤

/-- The zero endomorphism of a line is cyclic on any nonzero vector's span: the scalar line
is the minimal single-channel carrier. -/
theorem cyclicVector_zero_one_dim : CyclicVector (0 : Module.End ℂ ℂ) 1 := by
  rw [CyclicVector, eq_top_iff]
  intro c _
  have h1 : (1 : ℂ) ∈ Set.range fun n : ℕ => ((0 : Module.End ℂ ℂ) ^ n) 1 :=
    ⟨0, by simp⟩
  have hmem := Submodule.subset_span (R := ℂ) h1
  simpa using Submodule.smul_mem _ c hmem

/-- Powers of a self-adjoint endomorphism move across an invariant form. -/
private theorem invariant_pow {B : LinearMap.BilinForm ℂ V} {K : Module.End ℂ V}
    (hK : ∀ x y, B (K x) y = B x (K y)) :
    ∀ (n : ℕ) (x y : V), B ((K ^ n) x) y = B x ((K ^ n) y) := by
  intro n
  induction n with
  | zero => intro x y; simp
  | succ n ih =>
    intro x y
    have h1 : (K ^ (n + 1)) x = (K ^ n) (K x) := by rw [pow_succ, Module.End.mul_apply]
    have h2 : (K ^ (n + 1)) y = K ((K ^ n) y) := by rw [pow_succ', Module.End.mul_apply]
    rw [h1, ih (K x) y, hK, ← h2]

/-- **Invariant forms on a cyclic module are symmetric**: on iterates of the cyclic vector the
form reads only the total power `i + j`. -/
theorem invariant_bilin_symm_of_cyclicVector {B : LinearMap.BilinForm ℂ V}
    {K : Module.End ℂ V} (hK : ∀ x y, B (K x) y = B x (K y)) {v : V}
    (hv : CyclicVector K v) (x y : V) : B x y = B y x := by
  have hbase : ∀ i j : ℕ, B ((K ^ i) v) ((K ^ j) v) = B ((K ^ j) v) ((K ^ i) v) := by
    intro i j
    rw [invariant_pow hK i, invariant_pow hK j, ← Module.End.mul_apply (K ^ i),
      ← Module.End.mul_apply (K ^ j), ← pow_add, ← pow_add, Nat.add_comm]
  have hxS : x ∈ Submodule.span ℂ (Set.range fun n : ℕ => (K ^ n) v) := by
    rw [hv]; exact Submodule.mem_top
  have hyS : y ∈ Submodule.span ℂ (Set.range fun n : ℕ => (K ^ n) v) := by
    rw [hv]; exact Submodule.mem_top
  have hinner : ∀ (j : ℕ) (z : V),
      z ∈ Submodule.span ℂ (Set.range fun n : ℕ => (K ^ n) v) →
      B z ((K ^ j) v) = B ((K ^ j) v) z := by
    intro j z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hbase i j
    | zero => simp
    | add a b ha hb iha ihb => simp [map_add, LinearMap.add_apply, iha, ihb]
    | smul c a ha iha => simp [map_smul, LinearMap.smul_apply, iha]
  induction hyS using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨j, rfl⟩ := hw
    exact hinner j x hxS
  | zero => simp
  | add a b ha hb iha ihb => simp [map_add, LinearMap.add_apply, iha, ihb]
  | smul c a ha iha => simp [map_smul, LinearMap.smul_apply, iha]

/-- **Alternating invariant forms on a cyclic module vanish.** -/
theorem isAlt_invariant_eq_zero_of_cyclicVector {B : LinearMap.BilinForm ℂ V}
    {K : Module.End ℂ V} (hK : ∀ x y, B (K x) y = B x (K y)) {v : V}
    (hv : CyclicVector K v) (halt : B.IsAlt) : B = 0 := by
  ext x y
  have hsymm := invariant_bilin_symm_of_cyclicVector hK hv x y
  have hskew := LinearMap.IsAlt.neg halt x y
  have h0 : B x y + B x y = 0 := by
    calc B x y + B x y = B y x + B x y := by rw [hsymm]
      _ = -(B x y) + B x y := by rw [← hskew]
      _ = 0 := by ring
  simpa using add_self_eq_zero.mp h0

/-- **The cyclic no-go.**  A symplectic structure — nondegenerate alternating form with `K`
self-adjoint — excludes cyclic vectors on any nontrivial carrier: the module of a symplectic
self-adjoint pair always has at least two channels. -/
theorem not_cyclicVector_of_symplectic [Nontrivial V] {B : LinearMap.BilinForm ℂ V}
    (hnd : B.Nondegenerate) (halt : B.IsAlt) {K : Module.End ℂ V}
    (hK : ∀ x y, B (K x) y = B x (K y)) (v : V) : ¬ CyclicVector K v := by
  intro hv
  have hB0 : B = 0 := isAlt_invariant_eq_zero_of_cyclicVector hK hv halt
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  refine hx (hnd.1 x fun n => ?_)
  rw [hB0]
  simp

end Cyclic

section RootSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Any endomorphism commuting with `K` preserves the generalized eigenspaces of `K`. -/
theorem mem_maxGenEigenspace_of_commute {L K : Module.End ℂ V} (h : Commute L K) (lam : ℂ) :
    ∀ x ∈ K.maxGenEigenspace lam, L x ∈ K.maxGenEigenspace lam := by
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  have hc : Commute L ((K - lam • 1) ^ n) :=
    ((h.sub_right ((Commute.one_right L).smul_right lam))).pow_right n
  calc ((K - lam • 1) ^ n) (L x)
      = ((K - lam • 1) ^ n * L) x := by rw [Module.End.mul_apply]
    _ = (L * (K - lam • 1) ^ n) x := by rw [hc.eq]
    _ = L (((K - lam • 1) ^ n) x) := by rw [Module.End.mul_apply]
    _ = 0 := by rw [hn, map_zero]

/-- The restriction of `K` to one of its generalized eigenspaces. -/
noncomputable def restrictMaxGen (K : Module.End ℂ V) (lam : ℂ) :
    Module.End ℂ ↥(K.maxGenEigenspace lam) :=
  K.restrict (mem_maxGenEigenspace_of_commute (Commute.refl K) lam)

/-- **No lone Jordan channel.**  For a symplectically self-adjoint endomorphism of a
finite-dimensional space, the restriction of `K` to any nontrivial generalized eigenspace has
no cyclic vector: every root space of the spectrum splits into at least two Jordan channels.
This strengthens even multiplicity — a single even Jordan block is excluded as well.  In
particular the canonical cyclic divisor model (multiplication on a one-generator jet algebra)
can never carry the symplectic symmetry at any eigenvalue. -/
theorem restrictMaxGen_no_cyclicVector_of_symplectic [FiniteDimensional ℂ V]
    (ω : LinearMap.BilinForm ℂ V) (hnd : ω.Nondegenerate) (halt : ω.IsAlt)
    (K : Module.End ℂ V) (hK : ∀ x y, ω (K x) y = ω x (K y)) (lam : ℂ)
    [Nontrivial ↥(K.maxGenEigenspace lam)] (v : ↥(K.maxGenEigenspace lam)) :
    ¬ CyclicVector (restrictMaxGen K lam) v := by
  refine not_cyclicVector_of_symplectic
    (nondegenerate_restrict_maxGenEigenspace ω hnd halt K hK lam)
    (isAlt_restrict ω halt _) ?_ v
  intro x y
  have hx := LinearMap.restrict_apply
    (mem_maxGenEigenspace_of_commute (Commute.refl K) lam) x
  have hy := LinearMap.restrict_apply
    (mem_maxGenEigenspace_of_commute (Commute.refl K) lam) y
  rw [restrictMaxGen, LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.restrict_apply,
    hx, hy]
  exact hK (x : V) (y : V)

end RootSpace

end RHTower
