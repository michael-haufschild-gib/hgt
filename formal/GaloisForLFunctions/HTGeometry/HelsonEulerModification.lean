import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.HTGeometry.DenseNullContinuationSeam

/-!
# Finite Euler modifications stay meromorphic on the plane

Changing the Euler factor of a zeta function at finitely many primes multiplies it by a finite
product of quotients of entire functions.  Such a product is meromorphic on the whole plane, so a
finite Euler modification of a function meromorphic on the plane is again meromorphic on the plane.

Applied to the Riemann zeta function this says that every phase agreeing with `1` at all but
finitely many primes carries a Helson zeta function with meromorphic continuation to `ℂ`.  Together
with the density of finite modifications in a product topology this is the dense half of the
continuation seam, and it uses no analytic input beyond the meromorphy of `ζ` itself.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- One Euler correction factor: the ratio of the unmodified factor to the modified one. -/
noncomputable def eulerFactor (a b : ℂ) : ℂ → ℂ :=
  fun s => (1 - a ^ (-s)) / (1 - b * a ^ (-s))

/-- A constant power with nonzero base is entire in the exponent. -/
theorem analyticAt_const_cpow_neg {a : ℂ} (ha : a ≠ 0) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => a ^ (-z)) s := by
  have hdiff : Differentiable ℂ fun z : ℂ => a ^ (-z) :=
    Differentiable.const_cpow differentiable_neg (Or.inl ha)
  exact hdiff.analyticAt s

theorem meromorphicAt_eulerFactor {a b : ℂ} (ha : a ≠ 0) (s : ℂ) :
    MeromorphicAt (eulerFactor a b) s := by
  have hnum : AnalyticAt ℂ (fun z : ℂ => 1 - a ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_const_cpow_neg ha s)
  have hden : AnalyticAt ℂ (fun z : ℂ => 1 - b * a ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const_cpow_neg ha s))
  exact hnum.meromorphicAt.div hden.meromorphicAt

/-- A finite product of functions meromorphic at a point is meromorphic there. -/
theorem meromorphicAt_finsetProd {ι : Type*} (P : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (hf : ∀ i ∈ P, MeromorphicAt (f i) s) :
    MeromorphicAt (fun z : ℂ => ∏ i ∈ P, f i z) s := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact (analyticAt_const (v := (1 : ℂ)) (x := s)).meromorphicAt
  | insert a P ha ih =>
      have hstep : (fun z : ℂ => ∏ i ∈ insert a P, f i z)
          = fun z : ℂ => f a z * ∏ i ∈ P, f i z := by
        funext z
        rw [Finset.prod_insert ha]
      rw [hstep]
      exact (hf a (Finset.mem_insert_self a P)).mul
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- **A finite Euler modification is meromorphic on the plane.** -/
theorem meromorphicOn_eulerModification {ι : Type*} (P : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ P, a i ≠ 0) :
    MeromorphicOn (fun s : ℂ => ∏ i ∈ P, eulerFactor (a i) (b i) s) Set.univ := by
  intro s _
  exact meromorphicAt_finsetProd P (fun i => eulerFactor (a i) (b i)) s
    fun i hi => meromorphicAt_eulerFactor (ha i hi) s

/-- **A finite Euler modification of a function meromorphic on the plane is meromorphic on the
plane.** -/
theorem meromorphicOn_mul_eulerModification {ι : Type*} {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (P : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ P, a i ≠ 0) :
    MeromorphicOn (fun s : ℂ => F s * ∏ i ∈ P, eulerFactor (a i) (b i) s) Set.univ := by
  intro s hs
  exact (hF s hs).mul (meromorphicOn_eulerModification P a b ha s hs)

/-- **Every finite Euler modification of the Riemann zeta function continues meromorphically to the
whole plane.** -/
theorem meromorphicOn_riemannZeta_mul_eulerModification {ι : Type*} (P : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ P, a i ≠ 0) :
    MeromorphicOn
      (fun s : ℂ => riemannZeta s * ∏ i ∈ P, eulerFactor (a i) (b i) s) Set.univ :=
  meromorphicOn_mul_eulerModification meromorphicOn_riemannZeta P a b ha

/-! ### The dense stratum of finitely modified phases -/

/-- The phases agreeing with the trivial phase at all but finitely many primes. -/
def finiteEulerStratum : Set (Nat.Primes → ℂ) :=
  GaloisForLFunctions.finiteModification (fun _ : Nat.Primes => ℂ) (fun _ => (1 : ℂ))

/-- **The finitely modified phases are dense.** -/
theorem dense_finiteEulerStratum : Dense finiteEulerStratum :=
  GaloisForLFunctions.dense_finiteModification _

/-- **Every finitely modified phase carries a presentation meromorphic on the whole plane.**  The
modified primes are exactly those where the phase differs from `1`, and outside them the Euler
factors are unchanged. -/
theorem exists_meromorphicOn_of_mem_finiteEulerStratum {χ : Nat.Primes → ℂ}
    (hχ : χ ∈ finiteEulerStratum) :
    ∃ P : Finset Nat.Primes, (∀ p, p ∉ P → χ p = 1) ∧
      MeromorphicOn
        (fun s : ℂ => riemannZeta s * ∏ p ∈ P, eulerFactor ((p : ℕ) : ℂ) (χ p) s) Set.univ := by
  classical
  have hfin : {p : Nat.Primes | χ p ≠ 1}.Finite := by
    simpa [finiteEulerStratum, GaloisForLFunctions.finiteModification] using hχ
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro p hp
    by_contra hne
    exact hp (hfin.mem_toFinset.mpr hne)
  · refine meromorphicOn_riemannZeta_mul_eulerModification _ _ _ ?_
    intro p _
    exact_mod_cast Nat.cast_ne_zero.mpr p.2.ne_zero

end GaloisForLFunctions.HTGeometry
