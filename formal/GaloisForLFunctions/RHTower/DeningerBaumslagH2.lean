import GaloisForLFunctions.RHTower.DeningerBaumslagFunctorial
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# `H²(R_U;ℚ) = 0` in mathlib's group cohomology

The splitting of central extensions is the content of the vanishing of second cohomology, and here
it is turned into that vanishing literally.  A normalized `2`-cocycle with values in a rational
vector space twists `M × G` into a central extension of `G` whose kernel is `M`, hence uniquely
divisible; the rationalization of a free group splits such an extension, and a section is exactly a
`1`-cochain trivializing the cocycle.

* `DeningerNormalizedCocycle`, `DeningerCocycleExt` : the twisted extension.
* `deningerCocycle_mem_coboundaries` : a normalized cocycle over `Bau(F)` is a coboundary.
* `deningerBauFree_H2_eq_zero` : `H²(Bau(F); M) = 0` for every rational vector space `M` with
  trivial action.
-/

namespace RHTower

open groupCohomology

section CocycleExtension

universe v

variable {G : Type} [Group G] {M : Type v} [AddCommGroup M]

/-- A normalized `2`-cocycle with values in a trivial module. -/
structure DeningerNormalizedCocycle (G : Type) [Group G] (M : Type v) [AddCommGroup M] where
  /-- The cocycle. -/
  f : G × G → M
  /-- The cocycle identity. -/
  cocycle : ∀ g h j : G, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)
  /-- Normalization in the first slot. -/
  one_fst : ∀ g : G, f (1, g) = 0
  /-- Normalization in the second slot. -/
  one_snd : ∀ g : G, f (g, 1) = 0

namespace DeningerNormalizedCocycle

variable (c : DeningerNormalizedCocycle G M)

theorem inv_symm (g : G) : c.f (g⁻¹, g) = c.f (g, g⁻¹) := by
  have h := c.cocycle g g⁻¹ g
  rw [mul_inv_cancel, inv_mul_cancel, c.one_fst, c.one_snd, zero_add, add_zero] at h
  exact h.symm

end DeningerNormalizedCocycle

/-- **The central extension of `G` by `M` twisted by a normalized cocycle.** -/
def DeningerCocycleExt (_c : DeningerNormalizedCocycle G M) : Type _ := M × G

namespace DeningerCocycleExt

variable {c : DeningerNormalizedCocycle G M}

/-- An element of the extension. -/
def mk (m : M) (g : G) : DeningerCocycleExt c := (m, g)

/-- The `M`-component. -/
def fst (x : DeningerCocycleExt c) : M := Prod.fst x

/-- The `G`-component. -/
def snd (x : DeningerCocycleExt c) : G := Prod.snd x

@[simp] theorem fst_mk (m : M) (g : G) : (mk m g : DeningerCocycleExt c).fst = m := rfl
@[simp] theorem snd_mk (m : M) (g : G) : (mk m g : DeningerCocycleExt c).snd = g := rfl
theorem eta (x : DeningerCocycleExt c) : mk x.fst x.snd = x := rfl

theorem ext_iff {x y : DeningerCocycleExt c} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2

instance : Mul (DeningerCocycleExt c) :=
  ⟨fun x y => mk (x.fst + y.fst + c.f (x.snd, y.snd)) (x.snd * y.snd)⟩

instance : One (DeningerCocycleExt c) := ⟨mk 0 1⟩

instance : Inv (DeningerCocycleExt c) :=
  ⟨fun x => mk (-x.fst - c.f (x.snd, x.snd⁻¹)) x.snd⁻¹⟩

@[simp] theorem mul_fst (x y : DeningerCocycleExt c) :
    (x * y).fst = x.fst + y.fst + c.f (x.snd, y.snd) := rfl

@[simp] theorem mul_snd (x y : DeningerCocycleExt c) : (x * y).snd = x.snd * y.snd := rfl

theorem mk_mul (m m' : M) (g g' : G) :
    (mk m g : DeningerCocycleExt c) * mk m' g' = mk (m + m' + c.f (g, g')) (g * g') := rfl

theorem one_eq : (1 : DeningerCocycleExt c) = mk 0 1 := rfl

theorem mk_inv (m : M) (g : G) :
    (mk m g : DeningerCocycleExt c)⁻¹ = mk (-m - c.f (g, g⁻¹)) g⁻¹ := rfl

instance : Group (DeningerCocycleExt c) where
  mul_assoc x y z := by
    rw [← eta x, ← eta y, ← eta z, mk_mul, mk_mul, mk_mul, mk_mul]
    refine congrArg₂ mk ?_ (mul_assoc _ _ _)
    have h' : c.f (x.snd * y.snd, z.snd) + c.f (x.snd, y.snd) =
        c.f (y.snd, z.snd) + c.f (x.snd, y.snd * z.snd) := c.cocycle _ _ _
    calc x.fst + y.fst + c.f (x.snd, y.snd) + z.fst + c.f (x.snd * y.snd, z.snd)
        = x.fst + y.fst + z.fst + (c.f (x.snd * y.snd, z.snd) + c.f (x.snd, y.snd)) := by abel
      _ = x.fst + y.fst + z.fst + (c.f (y.snd, z.snd) + c.f (x.snd, y.snd * z.snd)) := by rw [h']
      _ = x.fst + (y.fst + z.fst + c.f (y.snd, z.snd)) + c.f (x.snd, y.snd * z.snd) := by abel
  one_mul x := by
    rw [← eta x, one_eq, mk_mul, c.one_fst, add_zero, zero_add, one_mul]
  mul_one x := by
    rw [← eta x, one_eq, mk_mul, c.one_snd, add_zero, add_zero, mul_one]
  inv_mul_cancel x := by
    rw [← eta x, mk_inv, mk_mul, one_eq, c.inv_symm, inv_mul_cancel]
    refine congrArg₂ mk ?_ rfl
    abel

/-- The projection to the base. -/
def proj (c : DeningerNormalizedCocycle G M) : DeningerCocycleExt c →* G where
  toFun x := x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem proj_mk (m : M) (g : G) : proj c (mk m g) = g := rfl

theorem proj_surjective (c : DeningerNormalizedCocycle G M) :
    Function.Surjective (proj c) := fun g => ⟨mk 0 g, rfl⟩

theorem pow_fibre (m : M) : ∀ n : ℕ,
    (mk m (1 : G) : DeningerCocycleExt c) ^ n = mk (n • m) 1
  | 0 => by
    rw [pow_zero, zero_smul, one_eq]
  | n + 1 => by
    rw [pow_succ, pow_fibre m n, mk_mul, c.one_fst, add_zero, succ_nsmul, mul_one]

/-- **The kernel is central.** -/
theorem ker_le_center (c : DeningerNormalizedCocycle G M) :
    (proj c).ker ≤ Subgroup.center (DeningerCocycleExt c) := by
  intro x hx
  have hx1 : x.snd = 1 := hx
  refine Subgroup.mem_center_iff.2 fun y => ?_
  rw [← eta x, ← eta y, mk_mul, mk_mul, hx1]
  rw [c.one_fst, c.one_snd, add_zero, add_zero, one_mul, mul_one]
  exact congrArg₂ mk (add_comm _ _) rfl

/-- **The kernel is uniquely divisible**, being a rational vector space. -/
theorem ker_uniquelyDivisible [Module ℚ M] (c : DeningerNormalizedCocycle G M) :
    DeningerUniquelyDivisible ((proj c).ker : Subgroup (DeningerCocycleExt c)) := by
  intro n hn k
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hk1 : (k : DeningerCocycleExt c).snd = 1 := k.2
  have hmemroot : (mk ((n : ℚ)⁻¹ • (k : DeningerCocycleExt c).fst) (1 : G) :
      DeningerCocycleExt c) ∈ (proj c).ker := rfl
  refine ⟨⟨_, hmemroot⟩, ?_, ?_⟩
  · refine Subtype.ext ?_
    show (mk ((n : ℚ)⁻¹ • (k : DeningerCocycleExt c).fst) (1 : G) : DeningerCocycleExt c) ^ n =
      (k : DeningerCocycleExt c)
    rw [pow_fibre]
    refine ext_iff ?_ ?_
    · show n • ((n : ℚ)⁻¹ • (k : DeningerCocycleExt c).fst) = (k : DeningerCocycleExt c).fst
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    · show (1 : G) = (k : DeningerCocycleExt c).snd
      exact hk1.symm
  · intro y hy
    have hy1 : (y : DeningerCocycleExt c).snd = 1 := y.2
    have hyval : (mk (y : DeningerCocycleExt c).fst (1 : G) : DeningerCocycleExt c) ^ n =
        (k : DeningerCocycleExt c) := by
      rw [← hy1, eta]
      exact congrArg Subtype.val hy
    rw [pow_fibre] at hyval
    have h1 : n • (y : DeningerCocycleExt c).fst = (k : DeningerCocycleExt c).fst :=
      congrArg fst hyval
    rw [← Nat.cast_smul_eq_nsmul ℚ] at h1
    refine Subtype.ext (ext_iff ?_ ?_)
    · show (y : DeningerCocycleExt c).fst = (n : ℚ)⁻¹ • (k : DeningerCocycleExt c).fst
      rw [← h1, smul_smul, inv_mul_cancel₀ hn', one_smul]
    · show (y : DeningerCocycleExt c).snd = (1 : G)
      exact hy1

end DeningerCocycleExt

end CocycleExtension

section BaumslagH2

variable {ι : Type} {M : Type} [AddCommGroup M] [Module ℚ M]

/-- **A normalized cocycle over the rationalization of a free group is a coboundary.**  The
extension it twists is central with uniquely divisible kernel, hence split, and a section is the
trivializing cochain. -/
theorem deningerBauFree_cocycle_trivial
    (c : DeningerNormalizedCocycle (DeningerBau (FreeGroup ι)) M) :
    ∃ b : DeningerBau (FreeGroup ι) → M, ∀ g h, c.f (g, h) = b (g * h) - b g - b h := by
  obtain ⟨s, hs⟩ := deningerBauFree_centralExtension_splits
    (DeningerCocycleExt.proj c) (DeningerCocycleExt.proj_surjective c)
    (DeningerCocycleExt.ker_uniquelyDivisible c) (DeningerCocycleExt.ker_le_center c)
  have hsnd : ∀ g, (s g).snd = g := fun g => DFunLike.congr_fun hs g
  refine ⟨fun g => (s g).fst, fun g h => ?_⟩
  show c.f (g, h) = (s (g * h)).fst - (s g).fst - (s h).fst
  have hmul : (s (g * h)).fst = (s g).fst + (s h).fst + c.f ((s g).snd, (s h).snd) := by
    rw [s.map_mul]
    exact DeningerCocycleExt.mul_fst _ _
  rw [hsnd, hsnd] at hmul
  rw [hmul]
  abel

/-- **`H²(Bau(F); M) = 0`** for every rational vector space `M` with trivial action.  This is the
card's degree-two half of `(3)`, in mathlib's group cohomology. -/
theorem deningerBauFree_H2_eq_zero
    (x : (groupCohomology.H2 (Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M))) : x = 0 := by
  refine groupCohomology.H2_induction_on x fun y => ?_
  refine (groupCohomology.H2π_eq_zero_iff y).2 ?_
  have hρ : ∀ (g : DeningerBau (FreeGroup ι)) (m : M),
      ((Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M).ρ g) m = m := fun g m => by simp
  have hy := (groupCohomology.mem_cocycles₂_iff
    (A := Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M) (⇑y)).1 y.2
  set c₀ : M := y (1, 1) with hc₀
  have hcocyc : ∀ g h j : DeningerBau (FreeGroup ι),
      (y (g * h, j) - c₀) + (y (g, h) - c₀) = (y (h, j) - c₀) + (y (g, h * j) - c₀) := by
    intro g h j
    have h1 := hy g h j
    rw [hρ] at h1
    calc (y (g * h, j) - c₀) + (y (g, h) - c₀)
        = (y (g * h, j) + y (g, h)) - c₀ - c₀ := by abel
      _ = (y (h, j) + y (g, h * j)) - c₀ - c₀ := by rw [h1]
      _ = (y (h, j) - c₀) + (y (g, h * j) - c₀) := by abel
  have hone1 : ∀ g : DeningerBau (FreeGroup ι), y (1, g) - c₀ = 0 := by
    intro g
    rw [groupCohomology.cocycles₂_map_one_fst, hc₀, sub_self]
  have hone2 : ∀ g : DeningerBau (FreeGroup ι), y (g, 1) - c₀ = 0 := by
    intro g
    rw [groupCohomology.cocycles₂_map_one_snd, hρ, hc₀, sub_self]
  obtain ⟨b, hb⟩ := deningerBauFree_cocycle_trivial (M := M) (ι := ι)
    { f := fun p => y p - c₀
      cocycle := hcocyc
      one_fst := hone1
      one_snd := hone2 }
  refine ⟨fun g => c₀ - b g, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  rw [groupCohomology.d₁₂_hom_apply, hρ]
  have hbg : y (g, h) - c₀ = b (g * h) - b g - b h := hb g h
  show c₀ - b h - (c₀ - b (g * h)) + (c₀ - b g) = y (g, h)
  calc c₀ - b h - (c₀ - b (g * h)) + (c₀ - b g)
      = (b (g * h) - b g - b h) + c₀ := by abel
    _ = (y (g, h) - c₀) + c₀ := by rw [← hbg]
    _ = y (g, h) := by abel

end BaumslagH2

end RHTower
