import GaloisForLFunctions.ArithmeticCouplingTheory.MixedDifferencesSeeEveryZero
import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubgroupJumpKernels

/-!
# The coupling homotopy is crossing-free

Index-preserving deformations are the sign itself: along a path of Hermitian forms the negative
index changes only through a null vector. A rigidity theorem can make a path crossing-free only by
confining its null vectors. For coupled towers the confining theorem is the annihilation of
separable kernels by the coupling Laplacian (`lap_lap_eq_zero_of_coupling_eq_zero`).

Let `A` be coupling-free across two subgroups `H₁, H₂` (for instance the axial assembly of a
kernel `K`) and interpolate `K_t = A + t(K − A)` (`couplingHomotopy`). On `H₁H₂` the coupling form of
`K_t` is the ray `t · L_a L_b K` (`lap_lap_couplingHomotopy`). Hence:

* **Crossing-free ray** (`negIndex_lap_lap_couplingHomotopy`): for every `t > 0` the coupling form of
  `K_t` on `H₁H₂` has the index of the coupling form of `K`; at `t = 0` it vanishes identically
  (`lap_lap_couplingHomotopy_zero`). Every change of index of `K_t` itself is carried by the axial
  part.
* **For `ζ`** (`negIndex_lap_lap_couplingHomotopy_zeta`): on a two-prime lattice `⟨p, q⟩`, with the
  scales `a = p`, `b = q`, the coupling form of every interpolation between a coupling-free kernel and
  Weil's kernel has exactly `κ(K_ζ)` negative squares for all `t > 0`.
-/

open Complex Finset
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (realTests rightZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

section General

variable {G : Type*} [CommGroup G]

/-- The axial–coupled interpolation `K_t = A + t(K − A)`. -/
def couplingHomotopy (A K : G → ℂ) (t : ℝ) (g : G) : ℂ := A g + t * (K g - A g)

theorem lap_lap_linear (a b : G) (A K : G → ℂ) (t : ℝ) (g : G) :
    lap a (lap b (couplingHomotopy A K t)) g =
      lap a (lap b A) g + t * (lap a (lap b K) g - lap a (lap b A) g) := by
  simp only [lap_lap_apply, couplingHomotopy]; ring

/-- **On the coupled lattice the coupling form of the homotopy is a ray.** -/
theorem lap_lap_couplingHomotopy {A : G → ℂ} (K : G → ℂ) {H₁ H₂ : Subgroup G}
    (hA : ∀ u ∈ H₁, ∀ v ∈ H₂, coupling A u v = 0) {a b : G} (ha : a ∈ H₁) (hb : b ∈ H₂)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ H₁) (hg₂ : g₂ ∈ H₂) (t : ℝ) :
    lap a (lap b (couplingHomotopy A K t)) (g₁ * g₂) = t * lap a (lap b K) (g₁ * g₂) := by
  rw [lap_lap_linear, lap_lap_eq_zero_of_coupling_eq_zero hA ha hb hg₁ hg₂]; ring

/-- At the axial end the coupling form vanishes. -/
theorem lap_lap_couplingHomotopy_zero {A : G → ℂ} (K : G → ℂ) {H₁ H₂ : Subgroup G}
    (hA : ∀ u ∈ H₁, ∀ v ∈ H₂, coupling A u v = 0) {a b : G} (ha : a ∈ H₁) (hb : b ∈ H₂)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ H₁) (hg₂ : g₂ ∈ H₂) :
    lap a (lap b (couplingHomotopy A K 0)) (g₁ * g₂) = 0 := by
  rw [lap_lap_couplingHomotopy K hA ha hb hg₁ hg₂]; simp

/-- **The coupling homotopy is crossing-free.** On a subgroup `H` all of whose elements split as
`g₁g₂` with `g_i ∈ H_i`, the coupling form of `K_t` has the index of the coupling form of `K` for
every `t > 0`. -/
theorem negIndex_lap_lap_couplingHomotopy {A : G → ℂ} (K : G → ℂ) {H₁ H₂ H : Subgroup G}
    (hA : ∀ u ∈ H₁, ∀ v ∈ H₂, coupling A u v = 0) {a b : G} (ha : a ∈ H₁) (hb : b ∈ H₂)
    (hH : ∀ g ∈ H, ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, g = g₁ * g₂) {t : ℝ} (ht : 0 < t) :
    negIndex (lap a (lap b (couplingHomotopy A K t)) ∘ H.subtype) =
      negIndex (lap a (lap b K) ∘ H.subtype) := by
  have heq : lap a (lap b (couplingHomotopy A K t)) ∘ H.subtype =
      fun h => (t : ℂ) * (lap a (lap b K) ∘ H.subtype) h := by
    funext h
    obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := hH h h.2
    simp only [Function.comp_apply, Subgroup.coe_subtype, hg]
    exact lap_lap_couplingHomotopy K hA ha hb hg₁ hg₂ t
  rw [heq, negIndex_mul_pos_real ht]

end General

/-! ### Weil's kernel on a two-prime lattice -/

/-- Every element of `⟨p, q⟩` is a `p`-power times a `q`-power. -/
theorem mem_twoPrimeLattice_split {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {g : HeckeLattice}
    (hg : g ∈ twoPrimeLattice hp hq) :
    ∃ g₁ ∈ Subgroup.zpowers (primeElt hp), ∃ g₂ ∈ Subgroup.zpowers (primeElt hq), g = g₁ * g₂ := by
  obtain ⟨m, n, rfl⟩ := Subgroup.mem_closure_pair.mp hg
  exact ⟨_, Subgroup.zpow_mem_zpowers _ m, _, Subgroup.zpow_mem_zpowers _ n, rfl⟩

theorem primeElt_ne_one {p : ℕ} (hp : p.Prime) : primeElt hp ≠ 1 := by
  intro h
  have := scale_primeElt hp
  rw [h, show scale heckeLogScale (1 : HeckeLattice) = 0 by simp [scale]] at this
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' this.symm

/-- **The coupling form of Weil's kernel on a two-prime lattice carries the whole index.** -/
theorem negIndex_lap_lap_zetaKernel_twoPrime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    negIndex (lap (primeElt hp) (lap (primeElt hq) zetaKernel) ∘ (twoPrimeLattice hp hq).subtype) =
      negIndex zetaKernel := by
  rw [zetaKernel, ← orbitKernel_mixedDiff _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      cubicSpline_mem_realTests,
    negIndex_orbitKernel_twoPrime _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      (mixedDiff_mem_realTests cubicSpline_mem_realTests _ _) hp hq hpq,
    seenRightZeros_mixedDiff _ cubicSpline_mem_realTests (scale_ne_zero (primeElt_ne_one hp))
      (scale_ne_zero (primeElt_ne_one hq)),
    negIndex_orbitKernel _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      cubicSpline_mem_realTests]

/-- **The coupling homotopy of `ζ` is crossing-free.** For every kernel `A` that is coupling-free
across the towers `⟨p⟩, ⟨q⟩` and every `t > 0`, the coupling form of `A + t(K_ζ − A)` on `⟨p, q⟩`
has exactly `κ(K_ζ)` negative squares. -/
theorem negIndex_lap_lap_couplingHomotopy_zeta {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {A : HeckeLattice → ℂ}
    (hA : ∀ u ∈ Subgroup.zpowers (primeElt hp), ∀ v ∈ Subgroup.zpowers (primeElt hq),
      coupling A u v = 0) {t : ℝ} (ht : 0 < t) :
    negIndex (lap (primeElt hp) (lap (primeElt hq) (couplingHomotopy A zetaKernel t)) ∘
      (twoPrimeLattice hp hq).subtype) = negIndex zetaKernel := by
  rw [negIndex_lap_lap_couplingHomotopy zetaKernel hA (Subgroup.mem_zpowers _)
      (Subgroup.mem_zpowers _) (fun g hg => mem_twoPrimeLattice_split hp hq hg) ht,
    negIndex_lap_lap_zetaKernel_twoPrime hp hq hpq]

end GaloisForLFunctions.ArithmeticCouplingTheory
