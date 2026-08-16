import GaloisForLFunctions.HTGeometry.AddressCapacityBound

/-!
# Left-normed bracket layers

The span of the brackets of two spans is the span of the brackets of their generators, because the
bracket is bilinear.  Iterating from a generating family of size `m` produces the left-normed layers,
whose degree-`k` member is spanned by `m^k` explicit elements and therefore has dimension at most
`m^k`.

This is the concrete replacement for "the homogeneous degree-`k` part of the free Lie algebra is a
quotient of the tensor power": no tensor power is needed, only bilinearity.
-/

open Finset Module Submodule

namespace GaloisForLFunctions.HTGeometry

section Bracket

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The span of all brackets of members of two subspaces. -/
def bracketSpan (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (A C : Submodule ℝ V) : Submodule ℝ V :=
  Submodule.span ℝ {z : V | ∃ x ∈ A, ∃ y ∈ C, z = B x y}

/-- **Bilinearity moves the span outside the bracket.** -/
theorem bracketSpan_span_range {ι κ : Type*} (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (a : ι → V) (c : κ → V) :
    bracketSpan B (Submodule.span ℝ (Set.range a)) (Submodule.span ℝ (Set.range c))
      = Submodule.span ℝ (Set.range fun p : ι × κ => B (a p.1) (c p.2)) := by
  refine le_antisymm ?_ ?_
  · rw [bracketSpan, Submodule.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hgoal : ∀ u ∈ Submodule.span ℝ (Set.range a),
        B u y ∈ Submodule.span ℝ (Set.range fun p : ι × κ => B (a p.1) (c p.2)) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        have hinner : ∀ v ∈ Submodule.span ℝ (Set.range c),
            B (a i) v ∈ Submodule.span ℝ (Set.range fun p : ι × κ => B (a p.1) (c p.2)) := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem s hs =>
            obtain ⟨j, rfl⟩ := hs
            exact Submodule.subset_span ⟨(i, j), rfl⟩
          | zero => simp
          | add p q _ _ hp hq =>
            rw [map_add]
            exact Submodule.add_mem _ hp hq
          | smul r p _ hp =>
            rw [map_smul]
            exact Submodule.smul_mem _ _ hp
        exact hinner y hy
      | zero => simp
      | add p q _ _ hp hq =>
        rw [map_add, LinearMap.add_apply]
        exact Submodule.add_mem _ hp hq
      | smul r p _ hp =>
        rw [map_smul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ _ hp
    exact hgoal x hx
  · rw [Submodule.span_le]
    rintro z ⟨p, rfl⟩
    exact Submodule.subset_span
      ⟨a p.1, Submodule.subset_span ⟨p.1, rfl⟩, c p.2, Submodule.subset_span ⟨p.2, rfl⟩, rfl⟩

/-! ## The left-normed layers -/

variable {m : ℕ}

/-- The left-normed bracket word on a generating family. -/
def leftNormed (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V) :
    (k : ℕ) → (Fin (k + 1) → Fin m) → V
  | 0, w => e (w 0)
  | (k + 1), w => B (e (w 0)) (leftNormed B e k fun i => w i.succ)

/-- The degree-`k` left-normed layer. -/
def bracketLayer (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V) (k : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (leftNormed B e k))

/-- **The layer bound.**  The degree-`k` left-normed layer has dimension at most `m^{k+1}`. -/
theorem finrank_bracketLayer_le (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V) (k : ℕ) :
    finrank ℝ ↥(bracketLayer B e k) ≤ m ^ (k + 1) := by
  refine le_trans (finrank_span_range_le (leftNormed B e k)) ?_
  simp

/-- The zeroth layer is the span of the generators. -/
theorem bracketLayer_zero (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V) :
    bracketLayer B e 0 = Submodule.span ℝ (Set.range e) := by
  rw [bracketLayer]
  congr 1
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w 0, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨fun _ => i, rfl⟩

end Bracket

/-! ## Every bracket shape reduces to left-normed words -/

section Jacobi

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

theorem mem_bracketSpan_of_mem {B : V →ₗ[ℝ] V →ₗ[ℝ] V} {A C : Submodule ℝ V} {x y : V}
    (hx : x ∈ A) (hy : y ∈ C) : B x y ∈ bracketSpan B A C :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem leftNormed_cons (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V) (k : ℕ) (i : Fin m)
    (v : Fin (k + 1) → Fin m) :
    leftNormed B e (k + 1) (Fin.cons i v) = B (e i) (leftNormed B e k v) := by
  simp [leftNormed]

/-- Bracketing a generator into a layer lands in the next layer. -/
theorem bracketSpan_zero_le (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V) (b : ℕ) :
    bracketSpan B (bracketLayer B e 0) (bracketLayer B e b) ≤ bracketLayer B e (b + 1) := by
  rw [bracketLayer, bracketLayer, bracketSpan_span_range, Submodule.span_le]
  rintro z ⟨p, rfl⟩
  refine Submodule.subset_span ⟨Fin.cons (p.1 0) p.2, ?_⟩
  rw [leftNormed_cons]
  rfl

/-- **The Jacobi reduction.**  The bracket of two left-normed layers lies in the left-normed layer of
the summed degree, so every bracket shape reduces to left-normed words. -/
theorem bracketSpan_bracketLayer_le (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : Fin m → V)
    (hjac : ∀ x y z : V, B x (B y z) = B (B x y) z + B y (B x z)) :
    ∀ a b : ℕ, bracketSpan B (bracketLayer B e a) (bracketLayer B e b)
      ≤ bracketLayer B e (a + b + 1) := by
  intro a
  induction a with
  | zero =>
    intro b
    simpa using bracketSpan_zero_le B e b
  | succ a ih =>
    intro b
    rw [bracketLayer, bracketLayer, bracketSpan_span_range, Submodule.span_le]
    rintro z ⟨p, rfl⟩
    set x : V := e (p.1 0) with hx
    set A : V := leftNormed B e a (fun i => p.1 i.succ) with hA
    set Y : V := leftNormed B e b p.2 with hY
    have hxmem : x ∈ bracketLayer B e 0 := by
      rw [bracketLayer_zero]
      exact Submodule.subset_span ⟨p.1 0, rfl⟩
    have hAmem : A ∈ bracketLayer B e a := Submodule.subset_span ⟨_, rfl⟩
    have hYmem : Y ∈ bracketLayer B e b := Submodule.subset_span ⟨_, rfl⟩
    have h1 : B A Y ∈ bracketLayer B e (a + b + 1) :=
      ih b (mem_bracketSpan_of_mem hAmem hYmem)
    have h2 : B x (B A Y) ∈ bracketLayer B e (a + b + 2) := by
      have h := bracketSpan_zero_le B e (a + b + 1) (mem_bracketSpan_of_mem hxmem h1)
      simpa [Nat.add_assoc] using h
    have h3 : B x Y ∈ bracketLayer B e (b + 1) :=
      bracketSpan_zero_le B e b (mem_bracketSpan_of_mem hxmem hYmem)
    have h4 : B A (B x Y) ∈ bracketLayer B e (a + b + 2) := by
      have h := ih (b + 1) (mem_bracketSpan_of_mem hAmem h3)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hval : leftNormed B e (a + 1) p.1 = B x A := by
      rw [leftNormed]
    have hjacobi : B (B x A) Y = B x (B A Y) - B A (B x Y) :=
      eq_sub_of_add_eq (hjac x A Y).symm
    dsimp only
    rw [hval, hjacobi]
    have hgoal : bracketLayer B e (a + 1 + b + 1) = bracketLayer B e (a + b + 2) := by
      congr 1
      omega
    rw [hgoal]
    exact Submodule.sub_mem _ h2 h4

end Jacobi


end GaloisForLFunctions.HTGeometry
