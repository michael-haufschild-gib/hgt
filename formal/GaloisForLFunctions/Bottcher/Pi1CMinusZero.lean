/-
# The fundamental group of `ℂ ∖ {0}` is `ℤ`

Mathlib computes no nontrivial fundamental group: `BranchLogRoot`/`RiemannMapping` only ever use the
simply-connected (trivial `π₁`) case. This file builds the first nontrivial one — `π₁(ℂ*) ≅ ℤ` — from
the universal cover `exp : ℂ → ℂ*` (`Complex.isCoveringMap_exp`; `ℂ` is simply connected, for free) and
Mathlib's monodromy/path-lifting API.

The map is the **degree / monodromy orbit map** `deg : π₁(ℂ*, 1) → exp⁻¹{1}`, `[γ] ↦` (endpoint of the
lift of `γ` starting at `0`). It is a bijection (injectivity from `ℂ` simply connected; surjectivity
from `ℂ` path-connected), and the fiber `exp⁻¹{1} = 2πi·ℤ` is `≅ ℤ`.

This is the foundation for the winding-divisibility that controls single-valued roots on annuli.
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Topology unitInterval

namespace Pi1CMinusZero

/-- The punctured plane `ℂ ∖ {0}` as a subtype. -/
abbrev Cs := {w : ℂ // w ≠ 0}

/-- The universal covering `exp : ℂ → ℂ*`. -/
noncomputable def pexp : ℂ → Cs := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩

theorem continuous_pexp : Continuous pexp :=
  Complex.continuous_exp.subtype_mk _

theorem covexp : IsCoveringMap pexp := Complex.isCoveringMap_exp

/-- The base point `1 ∈ ℂ*`. -/
def one_cs : Cs := ⟨1, one_ne_zero⟩

@[simp] theorem pexp_zero : pexp 0 = one_cs := by simp [pexp, one_cs]

theorem mem_fiber_iff (z : ℂ) : pexp z ∈ ({one_cs} : Set Cs) ↔ Complex.exp z = 1 := by
  simp [pexp, one_cs, Subtype.ext_iff]

/-- `ℂ` is simply connected (it is contractible), the universal-cover hypothesis. -/
example : SimplyConnectedSpace ℂ := inferInstance

theorem twopiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- `exp (n · 2πi) = 1`, i.e. `n·2πi` is a fiber point over `1`. -/
theorem pexp_zmul (n : ℤ) : pexp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = one_cs := by
  apply Subtype.ext
  show Complex.exp _ = (1 : ℂ)
  rw [Complex.exp_eq_one_iff]; exact ⟨n, rfl⟩

theorem zmul_mem_fiber (n : ℤ) :
    ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ∈ pexp ⁻¹' {one_cs} := by
  rw [Set.mem_preimage, Set.mem_singleton_iff, pexp_zmul]

/-- The integer index of a fiber point `e` over `1`: the `n` with `e = n·2πi`. -/
noncomputable def degOfFiber (e : pexp ⁻¹' {one_cs}) : ℤ :=
  (Complex.exp_eq_one_iff.mp ((mem_fiber_iff e.1).mp e.2)).choose

theorem degOfFiber_spec (e : pexp ⁻¹' {one_cs}) :
    (e : ℂ) = ((degOfFiber e : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
  (Complex.exp_eq_one_iff.mp ((mem_fiber_iff e.1).mp e.2)).choose_spec

/-- The fiber `exp⁻¹{1} = { z : exp z = 1 }` is in bijection with `ℤ` (`z = n·2πi`). -/
noncomputable def fiberEquivInt : (pexp ⁻¹' {one_cs}) ≃ ℤ :=
  Equiv.ofBijective degOfFiber
    ⟨fun a b hab => by
        apply Subtype.ext
        rw [degOfFiber_spec a, degOfFiber_spec b, hab],
     fun n => ⟨⟨_, zmul_mem_fiber n⟩, by
        have h := degOfFiber_spec (⟨_, zmul_mem_fiber n⟩ : pexp ⁻¹' {one_cs})
        have hnc : (n : ℂ) = (degOfFiber (⟨_, zmul_mem_fiber n⟩ : pexp ⁻¹' {one_cs}) : ℂ) :=
          mul_right_cancel₀ twopiI_ne_zero h
        exact_mod_cast hnc.symm⟩⟩

/-- The base lift `0 ∈ ℂ` of `1 ∈ ℂ*`. -/
def e0 : pexp ⁻¹' {one_cs} := ⟨0, by rw [Set.mem_preimage, Set.mem_singleton_iff, pexp_zero]⟩

/-- The **monodromy / degree orbit map** `π₁(ℂ*,1) → exp⁻¹{1}`: send a loop class to the endpoint of
its lift starting at `0`. -/
noncomputable def degClass (γ : Path.Homotopic.Quotient one_cs one_cs) : pexp ⁻¹' {one_cs} :=
  covexp.monodromy γ e0

/-- The full integer degree of a loop class. -/
noncomputable def degZ (γ : Path.Homotopic.Quotient one_cs one_cs) : ℤ :=
  fiberEquivInt (degClass γ)

/-- **Deck translation.** A lift of a loop `γ` (based at `1`) starting at a fiber point `e` ends at
`e + (endpoint of the lift starting at 0)`. Reason: `exp(e + ·) = exp e · exp(·) = exp(·)` on the
fiber (`exp e = 1`), so `t ↦ e + Γ(t)` (with `Γ` the lift from `0`) is *the* lift from `e`. -/
theorem monodromy_translate (p : Path one_cs one_cs) (e : pexp ⁻¹' {one_cs}) :
    ((covexp.monodromy ⟦p⟧ e : ℂ)) = (e : ℂ) + (covexp.monodromy ⟦p⟧ e0 : ℂ) := by
  -- the canonical lift from 0
  set Γ : C(I, ℂ) := covexp.liftPath p (e0 : ℂ)
    ((p.source).trans e0.2.symm) with hΓ
  -- the translated path from e
  have hexp_e : Complex.exp (e : ℂ) = 1 := (mem_fiber_iff e.1).mp e.2
  set Δ : C(I, ℂ) := ⟨fun t => (e : ℂ) + Γ t, by fun_prop⟩ with hΔ
  -- Δ is the lift of p starting at e
  have hΔlift : pexp ∘ Δ = p := by
    funext t
    have hg : pexp (Γ t) = p t := congr_fun (covexp.liftPath_lifts p (e0:ℂ) _) t
    apply Subtype.ext
    show Complex.exp ((e : ℂ) + Γ t) = (p t : ℂ)
    rw [Complex.exp_add, hexp_e, one_mul]
    exact congrArg Subtype.val hg
  have hΔ0 : Δ 0 = (e : ℂ) := by
    show (e : ℂ) + Γ 0 = (e : ℂ)
    rw [covexp.liftPath_zero p (e0:ℂ) _]; show (e:ℂ) + (e0:ℂ) = (e:ℂ)
    simp [e0]
  -- so Δ = liftPath p e, hence endpoints agree
  have hΔeq : Δ = covexp.liftPath p (e : ℂ) ((p.source).trans e.2.symm) :=
    (covexp.eq_liftPath_iff' _).mpr ⟨hΔlift, hΔ0⟩
  -- compute both monodromy endpoints
  have hmono_e : (covexp.monodromy ⟦p⟧ e : ℂ) = Δ 1 := by
    show (covexp.monodromy (Path.Homotopic.Quotient.mk p) e : ℂ) = _
    rw [hΔeq]; rfl
  have hmono_0 : (covexp.monodromy ⟦p⟧ e0 : ℂ) = Γ 1 := rfl
  rw [hmono_e, hmono_0]
  show (e : ℂ) + Γ 1 = (e : ℂ) + Γ 1
  rfl

/-- `degZ` is **additive** under loop composition. -/
theorem degZ_trans (a b : Path.Homotopic.Quotient one_cs one_cs) :
    degZ (a.trans b) = degZ a + degZ b := by
  induction a using Quotient.inductionOn with
  | _ pa =>
  induction b using Quotient.inductionOn with
  | _ pb =>
  -- translate the second monodromy off the first; the index of a sum is the sum of indices
  have hsum : (degClass (Path.Homotopic.Quotient.trans ⟦pa⟧ ⟦pb⟧) : ℂ)
      = (degClass ⟦pa⟧ : ℂ) + (degClass ⟦pb⟧ : ℂ) := by
    show (covexp.monodromy (Path.Homotopic.Quotient.trans ⟦pa⟧ ⟦pb⟧) e0 : ℂ) = _
    rw [covexp.monodromy_trans_apply ⟦pa⟧ ⟦pb⟧ e0,
      monodromy_translate pb (covexp.monodromy ⟦pa⟧ e0)]
    rfl
  have ea := degOfFiber_spec (degClass ⟦pa⟧)
  have eb := degOfFiber_spec (degClass ⟦pb⟧)
  have es := degOfFiber_spec (degClass (Path.Homotopic.Quotient.trans ⟦pa⟧ ⟦pb⟧))
  have hZ : ((degOfFiber (degClass (Path.Homotopic.Quotient.trans ⟦pa⟧ ⟦pb⟧)) : ℂ))
      = (degOfFiber (degClass ⟦pa⟧) : ℂ) + (degOfFiber (degClass ⟦pb⟧) : ℂ) := by
    rw [es, ea, eb] at hsum
    have h2 : ((degOfFiber (degClass (Path.Homotopic.Quotient.trans ⟦pa⟧ ⟦pb⟧)) : ℂ))
          * (2 * (Real.pi : ℂ) * Complex.I)
        = ((degOfFiber (degClass ⟦pa⟧) : ℂ) + (degOfFiber (degClass ⟦pb⟧) : ℂ))
            * (2 * (Real.pi : ℂ) * Complex.I) := by linear_combination hsum
    exact mul_right_cancel₀ twopiI_ne_zero h2
  show fiberEquivInt _ = fiberEquivInt _ + fiberEquivInt _
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hZ

/-- `degClass` is **surjective**: every fiber point is the lift-endpoint of some loop (`ℂ` is path
connected — take a path from `0` to the fiber point and project). -/
theorem degClass_surjective : Function.Surjective degClass := by
  intro e
  have hp1 : pexp (e : ℂ) = one_cs := (Set.mem_singleton_iff).mp e.2
  have hp0 : pexp (e0 : ℂ) = one_cs := pexp_zero
  set Γ : Path (e0 : ℂ) (e : ℂ) := PathConnectedSpace.somePath (e0 : ℂ) (e : ℂ) with hΓ
  -- project to a loop at `1`
  set p : Path one_cs one_cs := (Γ.map continuous_pexp).cast hp0.symm hp1.symm with hp
  refine ⟨⟦p⟧, ?_⟩
  apply Subtype.ext
  -- `Γ` itself is the lift of `p` starting at `0`
  have hlift : pexp ∘ (Γ.toContinuousMap) = p := by
    funext t
    show pexp (Γ t) = p t
    rw [hp, Path.cast_coe, Path.map_coe]; rfl
  have h0 : (Γ.toContinuousMap) 0 = (e0 : ℂ) := Γ.source
  have heq : (Γ.toContinuousMap) = covexp.liftPath p (e0 : ℂ) ((p.source).trans e0.2.symm) :=
    (covexp.eq_liftPath_iff' _).mpr ⟨hlift, h0⟩
  show (covexp.monodromy ⟦p⟧ e0 : ℂ) = (e : ℂ)
  have hcomp : (covexp.monodromy ⟦p⟧ e0 : ℂ)
      = (covexp.liftPath p (e0 : ℂ) ((p.source).trans e0.2.symm)) 1 := rfl
  rw [hcomp, ← heq]
  exact Γ.target

/-- `degClass` is **injective**: two loops with the same lift-endpoint are homotopic (lift both to `ℂ`,
which is simply connected, so the two lifts are homotopic rel endpoints; project back down). -/
theorem degClass_injective : Function.Injective degClass := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ pa =>
  induction b using Quotient.inductionOn with
  | _ pb =>
  apply Quotient.sound
  -- the two lifts from `0`
  set Γa : C(I, ℂ) := covexp.liftPath pa (e0 : ℂ) ((pa.source).trans e0.2.symm) with hΓa
  set Γb : C(I, ℂ) := covexp.liftPath pb (e0 : ℂ) ((pb.source).trans e0.2.symm) with hΓb
  have hla : pexp ∘ Γa = pa := covexp.liftPath_lifts pa (e0 : ℂ) _
  have hlb : pexp ∘ Γb = pb := covexp.liftPath_lifts pb (e0 : ℂ) _
  have h0a : Γa 0 = (e0 : ℂ) := covexp.liftPath_zero pa (e0 : ℂ) _
  have h0b : Γb 0 = (e0 : ℂ) := covexp.liftPath_zero pb (e0 : ℂ) _
  have hend : Γa 1 = Γb 1 := congrArg Subtype.val hab
  -- as paths in `ℂ` from `0` to the common endpoint
  set Pa : Path (e0 : ℂ) (Γa 1) := ⟨Γa, h0a, rfl⟩ with hPa
  set Pb : Path (e0 : ℂ) (Γa 1) := ⟨Γb, h0b, hend.symm⟩ with hPb
  have hHom : Pa.Homotopic Pb := SimplyConnectedSpace.paths_homotopic Pa Pb
  -- project the homotopy down through `pexp`
  have hmap := hHom.map ⟨pexp, continuous_pexp⟩
  -- endpoint identifications for the cast back to loops at `1`
  have h1 : one_cs = pexp (e0 : ℂ) := (pexp_zero).symm
  have h2 : one_cs = pexp (Γa 1) := ((congr_fun hla 1).trans pa.target).symm
  have hcastA : (Pa.map (ContinuousMap.continuous ⟨pexp, continuous_pexp⟩)).cast h1 h2 = pa := by
    apply Path.ext; funext t; exact congr_fun hla t
  have hcastB : (Pb.map (ContinuousMap.continuous ⟨pexp, continuous_pexp⟩)).cast h1 h2 = pb := by
    apply Path.ext; funext t; exact congr_fun hlb t
  have hcast := Path.Homotopic.pathCast hmap h1 h2
  rwa [hcastA, hcastB] at hcast

/-- **`degClass` is a bijection.** -/
theorem degClass_bijective : Function.Bijective degClass :=
  ⟨degClass_injective, degClass_surjective⟩

/-- The full integer degree `π₁(ℂ*,1) → ℤ` is **surjective**. -/
theorem degZ_surjective : Function.Surjective degZ := by
  intro n
  obtain ⟨γ, hγ⟩ := degClass_surjective (fiberEquivInt.symm n)
  exact ⟨γ, by rw [degZ, hγ, Equiv.apply_symm_apply]⟩

/-- **`π₁(ℂ*, 1) ≅ ℤ` as a set.** The degree/monodromy orbit map is a bijection of `π₁(ℂ*,1)` with the
fiber `exp⁻¹{1} ≅ ℤ`. Combined with `degZ_trans` (additivity) this is the group isomorphism
`π₁(ℂ*) ≅ ℤ`. -/
noncomputable def pi1Equiv : Path.Homotopic.Quotient one_cs one_cs ≃ ℤ :=
  (Equiv.ofBijective degClass degClass_bijective).trans fiberEquivInt

theorem pi1Equiv_apply (γ : Path.Homotopic.Quotient one_cs one_cs) : pi1Equiv γ = degZ γ := rfl

/-- **`π₁(ℂ*) ≅ ℤ`, as a group isomorphism.** The bijection `pi1Equiv` carries loop composition
(`Path.Homotopic.Quotient.trans`) to integer addition (`degZ_trans`). -/
theorem pi1Equiv_trans (a b : Path.Homotopic.Quotient one_cs one_cs) :
    pi1Equiv (a.trans b) = pi1Equiv a + pi1Equiv b := by
  simpa only [pi1Equiv_apply] using degZ_trans a b

/-! ## Squaring doubles the degree

The covering `sq : ℂ* → ℂ*`, `w ↦ w²`, induces multiplication by `2` on `π₁(ℂ*) ≅ ℤ`. Reason: `sq`
lifts through the universal cover as doubling — `sq (exp z) = exp (2z)` — so the lift of `sq ∘ p` from
`0` is `2 ·` the lift of `p`, doubling the monodromy endpoint. This is the algebraic heart of
"single-valued square root ⟺ even winding": the squares in `π₁(ℂ*)` are exactly the even loops. -/

/-- The continuous squaring map on `ℂ*`. -/
def sqCs : Cs → Cs := fun w => ⟨(w : ℂ) ^ 2, pow_ne_zero 2 w.2⟩

theorem continuous_sqCs : Continuous sqCs :=
  (by fun_prop : Continuous fun w : Cs => ((w : ℂ) ^ 2)).subtype_mk _

@[simp] theorem sqCs_one : sqCs one_cs = one_cs := by
  apply Subtype.ext; simp [sqCs, one_cs]

/-- `exp` conjugates doubling to squaring: `exp (2z) = (exp z)²`. -/
theorem pexp_two_mul (z : ℂ) : pexp (2 * z) = sqCs (pexp z) := by
  apply Subtype.ext
  show Complex.exp (2 * z) = (Complex.exp z) ^ 2
  rw [two_mul, Complex.exp_add, sq]

/-- The image of a loop class under `sq`, as a loop class based at `1` (`sq 1 = 1`). -/
noncomputable def sqLoop (p : Path one_cs one_cs) : Path one_cs one_cs :=
  (p.map continuous_sqCs).cast sqCs_one.symm sqCs_one.symm

/-- **Squaring doubles the degree:** `deg(sq ∘ p) = 2 · deg(p)`. The lift of `sq ∘ p` from `0` is `2 ·`
the lift of `p` (since `sq (exp ·) = exp (2 ·)`), so its endpoint — the monodromy class — doubles. -/
theorem degZ_sqLoop (p : Path one_cs one_cs) :
    degZ ⟦sqLoop p⟧ = 2 * degZ ⟦p⟧ := by
  -- the canonical lift of `p` from `0`
  set Γ : C(I, ℂ) := covexp.liftPath p (e0 : ℂ) ((p.source).trans e0.2.symm) with hΓ
  have hl : pexp ∘ Γ = p := covexp.liftPath_lifts p (e0 : ℂ) _
  have h0 : Γ 0 = (e0 : ℂ) := covexp.liftPath_zero p (e0 : ℂ) _
  -- the doubled lift
  set Δ : C(I, ℂ) := ⟨fun t => 2 * Γ t, by fun_prop⟩ with hΔ
  -- `Δ` lifts `sqLoop p`
  have hΔl : pexp ∘ Δ = sqLoop p := by
    funext t
    show pexp (2 * Γ t) = sqLoop p t
    have hlt : pexp (Γ t) = p t := congr_fun hl t
    rw [pexp_two_mul, hlt]
    show sqCs (p t) = sqLoop p t
    rw [sqLoop, Path.cast_coe, Path.map_coe]
    rfl
  have hΔ0 : Δ 0 = (e0 : ℂ) := by
    show 2 * Γ 0 = (e0 : ℂ); rw [h0]; show 2 * (e0 : ℂ) = (e0 : ℂ); simp [e0]
  have hΔeq : Δ = covexp.liftPath (sqLoop p) (e0 : ℂ) (((sqLoop p).source).trans e0.2.symm) :=
    (covexp.eq_liftPath_iff' _).mpr ⟨hΔl, hΔ0⟩
  -- endpoints: the monodromy class of `sqLoop p` is `2 ·` that of `p`
  have e1 : (covexp.monodromy ⟦sqLoop p⟧ e0 : ℂ) = Δ 1 := by
    have h : (covexp.monodromy ⟦sqLoop p⟧ e0 : ℂ)
        = (covexp.liftPath (sqLoop p) (e0 : ℂ) (((sqLoop p).source).trans e0.2.symm)) 1 := rfl
    rw [h, ← hΔeq]
  have hcdeg : (degClass ⟦sqLoop p⟧ : ℂ) = 2 * (degClass ⟦p⟧ : ℂ) := by
    show (covexp.monodromy ⟦sqLoop p⟧ e0 : ℂ) = 2 * (covexp.monodromy ⟦p⟧ e0 : ℂ)
    rw [e1]; rfl
  -- pass to integer degrees via the fiber coordinate
  have hd := degOfFiber_spec (degClass ⟦sqLoop p⟧)
  have hp := degOfFiber_spec (degClass ⟦p⟧)
  have hZ : (degOfFiber (degClass ⟦sqLoop p⟧) : ℂ) = (2 * degOfFiber (degClass ⟦p⟧) : ℤ) := by
    have h2 : (degOfFiber (degClass ⟦sqLoop p⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = ((2 * degOfFiber (degClass ⟦p⟧) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [← hd]; push_cast; rw [hcdeg, hp]; ring
    exact mul_right_cancel₀ twopiI_ne_zero h2
  show fiberEquivInt _ = 2 * fiberEquivInt _
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hZ

/-! ## Winding is a homomorphism for pointwise loop multiplication

`ℂ*` is an abelian topological group, so beyond loop *composition* (`degZ_trans`) the degree is also
additive under *pointwise* multiplication of loops: `deg(γ · δ) = deg γ + deg δ`. Reason: `exp` is a
group homomorphism (`exp(a+b) = exp a · exp b`), so the lift of `γ · δ` from `0` is the *sum* of the
lifts of `γ` and `δ`. This single fact yields squaring-doubles (`δ = γ`), constant-invariance
(`deg(const) = 0`), and the Böttcher winding `deg(z·e^{S}) = deg(z)` — the dynamical bookkeeping. -/

/-- Pointwise product of two loops based at `1` (`ℂ*` is a group: `1·1 = 1`). -/
noncomputable def mulLoop (p q : Path one_cs one_cs) : Path one_cs one_cs where
  toFun := fun t => ⟨(p t : ℂ) * (q t : ℂ), mul_ne_zero (p t).2 (q t).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp p.continuous_toFun).mul
      (continuous_subtype_val.comp q.continuous_toFun)
  source' := by apply Subtype.ext; show (p 0 : ℂ) * (q 0 : ℂ) = (1 : ℂ); rw [p.source, q.source]; simp [one_cs]
  target' := by apply Subtype.ext; show (p 1 : ℂ) * (q 1 : ℂ) = (1 : ℂ); rw [p.target, q.target]; simp [one_cs]

/-- `exp` is a homomorphism: `exp (a + b) = exp a · exp b`, lifted to `ℂ*`. -/
theorem pexp_add (a b : ℂ) : (pexp (a + b) : ℂ) = (pexp a : ℂ) * (pexp b : ℂ) := by
  show Complex.exp (a + b) = Complex.exp a * Complex.exp b
  rw [Complex.exp_add]

/-- **Winding is additive under pointwise loop multiplication:** `deg(p · q) = deg p + deg q`. -/
theorem degZ_mulLoop (p q : Path one_cs one_cs) :
    degZ ⟦mulLoop p q⟧ = degZ ⟦p⟧ + degZ ⟦q⟧ := by
  set Γp : C(I, ℂ) := covexp.liftPath p (e0 : ℂ) ((p.source).trans e0.2.symm) with hΓp
  set Γq : C(I, ℂ) := covexp.liftPath q (e0 : ℂ) ((q.source).trans e0.2.symm) with hΓq
  have hlp : pexp ∘ Γp = p := covexp.liftPath_lifts p (e0 : ℂ) _
  have hlq : pexp ∘ Γq = q := covexp.liftPath_lifts q (e0 : ℂ) _
  have h0p : Γp 0 = (e0 : ℂ) := covexp.liftPath_zero p (e0 : ℂ) _
  have h0q : Γq 0 = (e0 : ℂ) := covexp.liftPath_zero q (e0 : ℂ) _
  -- the summed lift
  set Δ : C(I, ℂ) := ⟨fun t => Γp t + Γq t, by fun_prop⟩ with hΔ
  have hΔl : pexp ∘ Δ = mulLoop p q := by
    funext t
    apply Subtype.ext
    show (pexp (Γp t + Γq t) : ℂ) = ((mulLoop p q) t : ℂ)
    rw [pexp_add]
    have hpt : (pexp (Γp t) : ℂ) = (p t : ℂ) := congrArg Subtype.val (congr_fun hlp t)
    have hqt : (pexp (Γq t) : ℂ) = (q t : ℂ) := congrArg Subtype.val (congr_fun hlq t)
    rw [hpt, hqt]; rfl
  have hΔ0 : Δ 0 = (e0 : ℂ) := by
    show Γp 0 + Γq 0 = (e0 : ℂ); rw [h0p, h0q]; show (e0 : ℂ) + (e0 : ℂ) = (e0 : ℂ); simp [e0]
  have hΔeq : Δ = covexp.liftPath (mulLoop p q) (e0 : ℂ) (((mulLoop p q).source).trans e0.2.symm) :=
    (covexp.eq_liftPath_iff' _).mpr ⟨hΔl, hΔ0⟩
  have e1 : (covexp.monodromy ⟦mulLoop p q⟧ e0 : ℂ) = Δ 1 := by
    have h : (covexp.monodromy ⟦mulLoop p q⟧ e0 : ℂ)
        = (covexp.liftPath (mulLoop p q) (e0 : ℂ) (((mulLoop p q).source).trans e0.2.symm)) 1 := rfl
    rw [h, ← hΔeq]
  have hcdeg : (degClass ⟦mulLoop p q⟧ : ℂ) = (degClass ⟦p⟧ : ℂ) + (degClass ⟦q⟧ : ℂ) := by
    show (covexp.monodromy ⟦mulLoop p q⟧ e0 : ℂ)
      = (covexp.monodromy ⟦p⟧ e0 : ℂ) + (covexp.monodromy ⟦q⟧ e0 : ℂ)
    rw [e1]; rfl
  have hd := degOfFiber_spec (degClass ⟦mulLoop p q⟧)
  have hp := degOfFiber_spec (degClass ⟦p⟧)
  have hq := degOfFiber_spec (degClass ⟦q⟧)
  have hZ : (degOfFiber (degClass ⟦mulLoop p q⟧) : ℂ)
      = ((degOfFiber (degClass ⟦p⟧) + degOfFiber (degClass ⟦q⟧) : ℤ) : ℂ) := by
    have h2 : (degOfFiber (degClass ⟦mulLoop p q⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = ((degOfFiber (degClass ⟦p⟧) + degOfFiber (degClass ⟦q⟧) : ℤ) : ℂ)
          * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [← hd]; push_cast; rw [hcdeg, hp, hq]; ring
    exact mul_right_cancel₀ twopiI_ne_zero h2
  show fiberEquivInt _ = fiberEquivInt _ + fiberEquivInt _
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hZ

/-- The constant loop has degree `0`: its lift from `0` is constant, ending at `0 = e0`. -/
theorem degZ_refl : degZ ⟦Path.refl one_cs⟧ = 0 := by
  have hmono : (covexp.monodromy ⟦Path.refl one_cs⟧ e0 : ℂ) = (e0 : ℂ) := by
    -- the constant lift `t ↦ 0` lifts `refl` and starts at `0`
    set Δ : C(I, ℂ) := ⟨fun _ => (e0 : ℂ), continuous_const⟩ with hΔ
    have hΔl : pexp ∘ Δ = Path.refl one_cs := by
      funext t; show pexp (e0 : ℂ) = one_cs; show pexp 0 = one_cs; simp
    have hΔ0 : Δ 0 = (e0 : ℂ) := rfl
    have hΔeq : Δ = covexp.liftPath (Path.refl one_cs) (e0 : ℂ)
        (((Path.refl one_cs).source).trans e0.2.symm) :=
      (covexp.eq_liftPath_iff' _).mpr ⟨hΔl, hΔ0⟩
    have h : (covexp.monodromy ⟦Path.refl one_cs⟧ e0 : ℂ)
        = (covexp.liftPath (Path.refl one_cs) (e0 : ℂ)
            (((Path.refl one_cs).source).trans e0.2.symm)) 1 := rfl
    rw [h, ← hΔeq]; rfl
  show fiberEquivInt (degClass ⟦Path.refl one_cs⟧) = 0
  have hsp := degOfFiber_spec (degClass ⟦Path.refl one_cs⟧)
  have : (degOfFiber (degClass ⟦Path.refl one_cs⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    rw [← hsp]; show (covexp.monodromy ⟦Path.refl one_cs⟧ e0 : ℂ) = 0
    rw [hmono]; show (0 : ℂ) = 0; rfl
  have hz : (degOfFiber (degClass ⟦Path.refl one_cs⟧) : ℂ) = 0 :=
    (mul_eq_zero.mp this).resolve_right twopiI_ne_zero
  show fiberEquivInt _ = 0
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hz

/-- The `k`-fold pointwise power of a loop at `1`. -/
noncomputable def powLoop : ℕ → Path one_cs one_cs → Path one_cs one_cs
  | 0, _ => Path.refl one_cs
  | (k + 1), p => mulLoop p (powLoop k p)

/-- **Winding of a pointwise power:** `deg(p^k) = k · deg p`. -/
theorem degZ_powLoop (k : ℕ) (p : Path one_cs one_cs) :
    degZ ⟦powLoop k p⟧ = k * degZ ⟦p⟧ := by
  induction k with
  | zero =>
    show degZ ⟦powLoop 0 p⟧ = ((0 : ℕ) : ℤ) * degZ ⟦p⟧
    rw [Nat.cast_zero, zero_mul]; exact degZ_refl
  | succ k ih =>
    show degZ ⟦mulLoop p (powLoop k p)⟧ = (k + 1) * degZ ⟦p⟧
    rw [degZ_mulLoop, ih]; ring

/-- Cancel a nonzero power from the winding identity `deg(p^k) = k·deg(p)`. -/
theorem degZ_eq_of_powLoop_eq_mul (k : ℕ) (p : Path one_cs one_cs) (m : ℤ)
    (hk : (k : ℤ) ≠ 0) (h : degZ ⟦powLoop k p⟧ = (k : ℤ) * m) :
    degZ ⟦p⟧ = m := by
  have hd := degZ_powLoop k p
  rw [h] at hd
  exact (mul_left_cancel₀ hk hd).symm

/-- If a nonzero `k`-th power loop has winding `k`, then the root loop has winding `1`. -/
theorem degZ_eq_one_of_powLoop_eq_natCast (k : ℕ) (p : Path one_cs one_cs)
    (hk : (k : ℤ) ≠ 0) (h : degZ ⟦powLoop k p⟧ = (k : ℤ)) :
    degZ ⟦p⟧ = 1 := by
  exact degZ_eq_of_powLoop_eq_mul k p 1 hk (by simpa using h)

/-- If `L` lifts the loop `p` (i.e. `exp ∘ L = p`) and starts at `0`, then the monodromy class of `p`
is read off as the endpoint `L 1`. The reusable form of the lift-endpoint computation. -/
theorem degClass_eq_of_lift (p : Path one_cs one_cs) (L : C(I, ℂ))
    (hL : pexp ∘ L = p) (h0 : L 0 = (e0 : ℂ)) : (degClass ⟦p⟧ : ℂ) = L 1 := by
  have heq : L = covexp.liftPath p (e0 : ℂ) ((p.source).trans e0.2.symm) :=
    (covexp.eq_liftPath_iff' _).mpr ⟨hL, h0⟩
  show (covexp.monodromy ⟦p⟧ e0 : ℂ) = L 1
  have h : (covexp.monodromy ⟦p⟧ e0 : ℂ)
      = (covexp.liftPath p (e0 : ℂ) ((p.source).trans e0.2.symm)) 1 := rfl
  rw [h, ← heq]

/-- **A loop whose values stay in the right half-plane has winding `0`.** The principal `log` is a
continuous section of `exp` on `slitPlane ⊇ {Re > 0}`, giving a lift that begins and ends at `0`. This
is what makes a "small perturbation" factor like `1 + c/ℓ²` (which stays near `1`) windingless. -/
theorem degZ_zero_of_re_pos (p : Path one_cs one_cs) (hp : ∀ t : I, 0 < (p t : ℂ).re) :
    degZ ⟦p⟧ = 0 := by
  have hcont : Continuous fun t : I => Complex.log ((p t : ℂ)) :=
    (continuous_subtype_val.comp p.continuous_toFun).clog (fun t => Or.inl (hp t))
  set L : C(I, ℂ) := ⟨fun t => Complex.log ((p t : ℂ)), hcont⟩ with hLdef
  have hL : pexp ∘ L = p := by
    funext t; apply Subtype.ext
    show Complex.exp (Complex.log (p t)) = (p t : ℂ)
    exact Complex.exp_log (p t).2
  have h0 : L 0 = (e0 : ℂ) := by
    show Complex.log ((p 0 : ℂ)) = (e0 : ℂ); rw [p.source]; exact Complex.log_one
  have h1 : (L : I → ℂ) 1 = 0 := by
    show Complex.log ((p 1 : ℂ)) = 0; rw [p.target]; exact Complex.log_one
  have hc : (degClass ⟦p⟧ : ℂ) = L 1 := degClass_eq_of_lift p L hL h0
  rw [h1] at hc
  have hsp := degOfFiber_spec (degClass ⟦p⟧)
  have hzero : (degOfFiber (degClass ⟦p⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 :=
    hsp.symm.trans hc
  have hz : (degOfFiber (degClass ⟦p⟧) : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right twopiI_ne_zero
  show fiberEquivInt _ = 0
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hz

/-- The degree map is **injective** (it is the bijection `pi1Equiv`). -/
theorem degZ_injective : Function.Injective degZ :=
  fiberEquivInt.injective.comp degClass_injective

/-- **The squares in `π₁(ℂ*)` are exactly the even loops.** A loop class is `[sq ∘ p]` for some loop
`p` iff its degree is even. This is the `π₁`-level statement of "a single-valued square root exists iff
the winding number is even" — the criterion that `exists_sqrt_pullback_of_lift` consumes as `hlift`. -/
theorem degZ_even_iff_sq (γ : Path.Homotopic.Quotient one_cs one_cs) :
    Even (degZ γ) ↔ ∃ p : Path one_cs one_cs, γ = ⟦sqLoop p⟧ := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨pc, hp⟩ := degZ_surjective k
    induction pc using Quotient.inductionOn with
    | _ p =>
    refine ⟨p, ?_⟩
    apply degZ_injective
    rw [degZ_sqLoop, hp, hk]; ring
  · rintro ⟨p, rfl⟩
    exact ⟨degZ ⟦p⟧, by rw [degZ_sqLoop]; ring⟩

/-- Multiply a loop in `ℂ*` by a fixed basepoint. Used to undo the normalization
`w ↦ w / b` in transported winding loops. -/
noncomputable def mulBaseMap (b : Cs) : C(Cs, Cs) where
  toFun := fun w => ⟨(b : ℂ) * (w : ℂ), mul_ne_zero b.2 w.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

@[simp] theorem mulBaseMap_one (b : Cs) : mulBaseMap b one_cs = b := by
  apply Subtype.ext
  simp [mulBaseMap, one_cs]

/-- Scale a based loop at `1` to a loop based at `e`. -/
noncomputable def scaleLoop (e : Cs) (q : Path one_cs one_cs) : Path e e where
  toFun := fun t => ⟨(e : ℂ) * (q t : ℂ), mul_ne_zero e.2 (q t).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul (continuous_subtype_val.comp q.continuous_toFun)
  source' := by
    apply Subtype.ext
    show (e : ℂ) * (q 0 : ℂ) = (e : ℂ)
    rw [q.source]
    simp [one_cs]
  target' := by
    apply Subtype.ext
    show (e : ℂ) * (q 1 : ℂ) = (e : ℂ)
    rw [q.target]
    simp [one_cs]

/-- Multiplying a squared normalized loop by `e²` is the square of the loop scaled by `e`. -/
theorem map_mulBase_sqLoop_eq_scaled_sq (e : Cs) (q : Path one_cs one_cs) :
    ((sqLoop q).map (mulBaseMap (sqCs e)).continuous).cast
        (mulBaseMap_one (sqCs e)).symm (mulBaseMap_one (sqCs e)).symm =
      (scaleLoop e q).map continuous_sqCs := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (e : ℂ) ^ 2 * (q t : ℂ) ^ 2 = ((e : ℂ) * (q t : ℂ)) ^ 2
  ring

/-- **Even degree gives square-cover range.** If a loop class in `π₁(ℂ*,1)` has even integer degree,
then it lies in the image of the square map on fundamental groups. This is the `FundamentalGroup`
form of `degZ_even_iff_sq`, matching Mathlib's covering-lift criterion. -/
theorem mem_sq_range_of_even_deg (γ : FundamentalGroup Cs one_cs)
    (hEven : Even (degZ (FundamentalGroup.toPath γ))) :
    γ ∈ (FundamentalGroup.mapOfEq ⟨sqCs, continuous_sqCs⟩ sqCs_one).range := by
  obtain ⟨p, hp⟩ := (degZ_even_iff_sq (FundamentalGroup.toPath γ)).mp hEven
  refine ⟨FundamentalGroup.fromPath (.mk p), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  exact hp.symm

end Pi1CMinusZero
