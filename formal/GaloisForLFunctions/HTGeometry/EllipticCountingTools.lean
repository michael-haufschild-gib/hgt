import GaloisForLFunctions.HTGeometry.EllipticFundamentalPoles

/-!
# The two remaining tools for the elliptic counting argument

The argument that a lattice-periodic meromorphic function is differentially algebraic compares a
quadratically growing family of monomials `fⁱ (f')ʲ` against a linearly growing space of principal
parts.  Two ingredients are needed besides the principal-jet map:

* **`exists_ne_zero_ker_of_card_lt`** — a linear map between coordinate spaces whose source has more
  coordinates than its target kills a nonzero vector.  This is what turns the count into a relation.
* **`nonneg_order_poleFactor`** — multiplying by `(· − p)^d` makes the order nonnegative once the
  pole order is at most `d`, which is the hypothesis the principal-jet machinery consumes.

`meromorphicOrderAt_poleFactor_mul` is the underlying computation: the order of `(· − p)^d · g` at
`p` is `d` plus the order of `g`.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ### A linear map into a smaller coordinate space has a kernel vector -/

/-- **Dimension count.**  A linear map into a space of strictly smaller dimension kills a nonzero
vector. -/
theorem exists_ne_zero_ker_of_finrank_lt {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] W) (h : Module.finrank ℂ W < Module.finrank ℂ V) :
    ∃ v : V, v ≠ 0 ∧ T v = 0 := by
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  obtain ⟨v, hv, hvne⟩ := Submodule.ne_bot_iff _ |>.mp hker
  exact ⟨v, hvne, LinearMap.mem_ker.mp hv⟩

/-- **Dimension count in coordinates.**  More source coordinates than target coordinates forces a
nonzero kernel vector. -/
theorem exists_ne_zero_ker_of_card_lt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (h : Fintype.card κ < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ T c = 0 := by
  refine exists_ne_zero_ker_of_finrank_lt T ?_
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  exact h

/-! ### Clearing a pole of bounded order -/

/-- The order of `(· − p)^d · g` at `p` is `d` plus the order of `g`. -/
theorem meromorphicOrderAt_poleFactor_mul {g : ℂ → ℂ} {p : ℂ} {d : ℕ} (hg : MeromorphicAt g p) :
    meromorphicOrderAt (fun z => (z - p) ^ d * g z) p
      = (d : WithTop ℤ) + meromorphicOrderAt g p := by
  have hpow : MeromorphicAt (fun z : ℂ => (z - p) ^ d) p := by fun_prop
  have hmul : meromorphicOrderAt ((fun z : ℂ => (z - p) ^ d) * g) p
      = meromorphicOrderAt (fun z : ℂ => (z - p) ^ d) p + meromorphicOrderAt g p :=
    meromorphicOrderAt_mul hpow hg
  have hfun : (fun z => (z - p) ^ d * g z) = (fun z : ℂ => (z - p) ^ d) * g := rfl
  rw [hfun, hmul]
  congr 1
  exact meromorphicOrderAt_pow_id_sub_const

/-- **Clearing a pole.**  If the order of `g` at `p` is at least `−d`, multiplying by `(· − p)^d`
makes the order nonnegative — the hypothesis the principal-jet machinery consumes. -/
theorem nonneg_order_poleFactor {g : ℂ → ℂ} {p : ℂ} {d : ℕ} (hg : MeromorphicAt g p)
    (hord : (-(d : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g p) :
    0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g z) p := by
  rw [meromorphicOrderAt_poleFactor_mul hg]
  have hzero : (0 : WithTop ℤ) = (-(d : ℤ) : WithTop ℤ) + (d : WithTop ℤ) := by
    norm_cast
    simp
  rw [hzero, add_comm (d : WithTop ℤ) (meromorphicOrderAt g p)]
  exact add_le_add_left hord _

end GaloisForLFunctions.HTGeometry
