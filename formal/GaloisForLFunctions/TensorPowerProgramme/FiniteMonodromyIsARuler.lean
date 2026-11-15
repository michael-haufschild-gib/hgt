import GaloisForLFunctions.TensorPowerProgramme.ThePrimeNumberTheoremOfTheCharactersGivesTheirIndependence
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Finite monodromy is a ruler

A base with **finite monodromy** gives each point `x` a Frobenius class `frob x` in a finite set
`Γ` (the conjugacy classes of a finite Galois group), and each class is equidistributed in the
analytic form of Chebotarev's theorem: `Σ_{frob x = g} λ(x) N(x)^{−s} = c_g/(s − 1) + G_g(s)` with
density `c_g > 0` and `G_g` continuous on `Re s ≥ 1` (`IsFiniteMonodromyBase`). A datum over it has
traces `t(x) = Σ_i b_i φ_i(frob x) N(x)^{z_i}`: the mode `z_i` with multiplicity function `φ_i` on
`Γ`, the trace of the monodromy on its eigenspace.

Each class, with its weight divided by its density, is an abelian base with the trivial character
group (`isAbelianBase_fibre`), and on it the datum is a flow datum with coefficients `b_i φ_i(g)`.
The moment over the base is the finite sum of the moments over the classes, so it reads the width
exactly (`summable_classMomentTerm_iff`): the `k`-th tensor moment converges iff `σ > 1 + 2kW`,
with `W` the largest real part of a mode active in some class.

The residue classes mod `q` (the Frobenius classes of `ℚ(μ_q)`) form such a base
(`isFiniteMonodromyBase_residue`), by the prime number theorem in arithmetic progressions.

Finite monodromy, like abelian monodromy (`summable_twistMomentTerm_iff`), makes the pole law the
width itself: a pole law that does not know the parameters needs infinite non-abelian monodromy.
-/

open Complex Filter Topology
open scoped LSeries.notation

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {P Γ ι : Type*} [Fintype Γ] [Fintype ι]

/-- A **base with finite monodromy**: norms `N ≥ 1`, weights `λ ≥ 0` with convergent Dirichlet
series on `Re s > 1`, Frobenius classes `frob x ∈ Γ`, and Chebotarev equidistribution of every
class with positive density. -/
structure IsFiniteMonodromyBase (N lam : P → ℝ) (frob : P → Γ) : Prop where
  one_le_norm : ∀ x, 1 ≤ N x
  lam_nonneg : ∀ x, 0 ≤ lam x
  summable_lam : ∀ σ : ℝ, 1 < σ → Summable fun x => lam x * N x ^ (-σ)
  chebotarev : ∀ g : Γ, ∃ c : ℝ, 0 < c ∧ ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      ∑' x : {x // frob x = g}, (lam x : ℂ) * (N x : ℂ) ^ (-s) = G s + (c : ℂ) / (s - 1)

variable {N lam : P → ℝ} {frob : P → Γ}

/-- **A Frobenius class is an abelian base** with the trivial character group, once its weight is
divided by its density. -/
theorem isAbelianBase_fibre (hB : IsFiniteMonodromyBase N lam frob) (g : Γ) {c : ℝ} (hc : 0 < c)
    {G : ℂ → ℂ} (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hF : ∀ s : ℂ, 1 < s.re →
      ∑' x : {x // frob x = g}, (lam x : ℂ) * (N x : ℂ) ^ (-s) = G s + (c : ℂ) / (s - 1)) :
    IsAbelianBase (fun x : {x // frob x = g} => N x) (fun x => lam x / c)
      (fun (_ : PUnit) _ => (1 : ℂ)) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine IsAbelianBase.of_pnt (fun x => hB.one_le_norm x)
    (fun x => div_nonneg (hB.lam_nonneg x) hc.le) (fun σ hσ => ?_) (fun _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ => by simp) ?_
    (fun ψ hψ => absurd (Subsingleton.elim ψ 1) hψ)
  · have h := ((hB.summable_lam σ hσ).subtype {x | frob x = g}).div_const c
    refine h.congr fun x => ?_
    simp only [Function.comp_apply]
    ring
  · refine ⟨fun s => G s / c, hG.div_const _, fun s hs => ?_⟩
    have hsum : baseLSeries (fun x : {x // frob x = g} => N x) (fun x => lam x / c)
        (fun (_ : PUnit) _ => (1 : ℂ)) 1 s =
        (∑' x : {x // frob x = g}, (lam x : ℂ) * (N x : ℂ) ^ (-s)) / c := by
      rw [baseLSeries, ← tsum_div_const]
      congr 1
      funext x
      push_cast
      ring
    rw [hsum, hF s hs, add_div, div_div_cancel_left' hc', one_div]

/-- The trace `t(x) = Σ_i b_i φ_i(frob x) N(x)^{z_i}` of a datum with finite monodromy. -/
def classTrace (N : P → ℝ) (frob : P → Γ) (z b : ι → ℂ) (φ : ι → Γ → ℂ) (x : P) : ℂ :=
  ∑ i, b i * φ i (frob x) * (N x : ℂ) ^ z i

/-- The terms `λ(x) |t(x)|^{2k} N(x)^{−σ}` of the `k`-th tensor moment. -/
def classMomentTerm (N lam : P → ℝ) (frob : P → Γ) (z b : ι → ℂ) (φ : ι → Γ → ℂ) (k : ℕ)
    (σ : ℝ) (x : P) : ℝ :=
  lam x * ‖classTrace N frob z b φ x‖ ^ (2 * k) * N x ^ (-σ)

theorem classMomentTerm_nonneg (hB : IsFiniteMonodromyBase N lam frob) (z b : ι → ℂ)
    (φ : ι → Γ → ℂ) (k : ℕ) (σ : ℝ) (x : P) : 0 ≤ classMomentTerm N lam frob z b φ k σ x :=
  mul_nonneg (mul_nonneg (hB.lam_nonneg x) (pow_nonneg (norm_nonneg _) _))
    (Real.rpow_nonneg (by linarith [hB.one_le_norm x]) _)

/-- On the class `g` the moment is `c` times the moment of the flow datum with coefficients
`b_i φ_i(g)`. -/
theorem classMomentTerm_fibre (g : Γ) {c : ℝ} (hc : 0 < c) (z b : ι → ℂ) (φ : ι → Γ → ℂ)
    (k : ℕ) (σ : ℝ) (x : {x // frob x = g}) :
    classMomentTerm N lam frob z b φ k σ x =
      c * twistMomentTerm (fun x : {x // frob x = g} => N x) (fun x => lam x / c)
        (fun (_ : PUnit) _ => (1 : ℂ)) z (fun i => b i * φ i g) (fun _ => (1 : PUnit)) k σ x := by
  have htr : classTrace N frob z b φ x =
      twistTrace (fun x : {x // frob x = g} => N x) (fun (_ : PUnit) _ => (1 : ℂ)) z
        (fun i => b i * φ i g) (fun _ => (1 : PUnit)) x := by
    rw [classTrace, twistTrace, x.2]
    simp only [mul_one]
  rw [classMomentTerm, twistMomentTerm, htr]
  field_simp

/-- The moment over the base converges iff it converges on every class. -/
theorem summable_classMomentTerm_iff_fibres (hB : IsFiniteMonodromyBase N lam frob)
    (z b : ι → ℂ) (φ : ι → Γ → ℂ) (k : ℕ) (σ : ℝ) :
    Summable (classMomentTerm N lam frob z b φ k σ) ↔
      ∀ g : Γ, Summable fun x : {x // frob x = g} => classMomentTerm N lam frob z b φ k σ x := by
  rw [← (Equiv.sigmaFiberEquiv frob).summable_iff,
    summable_sigma_of_nonneg fun p => classMomentTerm_nonneg hB z b φ k σ _]
  exact ⟨fun h => h.1, fun h => ⟨h, Summable.of_finite⟩⟩

/-- **Finite monodromy is a ruler.** A datum over a base with finite monodromy, with distinct modes
and width `W` (the largest real part of a mode active in some class), has `k`-th tensor moment
converging exactly for `σ > 1 + 2kW`. -/
theorem summable_classMomentTerm_iff (hB : IsFiniteMonodromyBase N lam frob) {z b : ι → ℂ}
    {φ : ι → Γ → ℂ} {W : ℝ} (hW : ∀ i g, b i * φ i g ≠ 0 → (z i).re ≤ W)
    (hWa : ∃ i g, b i * φ i g ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → i = j) {k : ℕ} (hk : 1 ≤ k) (σ : ℝ) :
    Summable (classMomentTerm N lam frob z b φ k σ) ↔ 1 + 2 * k * W < σ := by
  rw [summable_classMomentTerm_iff_fibres hB]
  constructor
  · intro h
    obtain ⟨i₀, g₀, hne, hre⟩ := hWa
    obtain ⟨c, hc, G, hG, hF⟩ := hB.chebotarev g₀
    have hBg := isAbelianBase_fibre hB g₀ hc hG hF
    have hs : Summable (twistMomentTerm (fun x : {x // frob x = g₀} => N x) (fun x => lam x / c)
        (fun (_ : PUnit) _ => (1 : ℂ)) z (fun i => b i * φ i g₀) (fun _ => (1 : PUnit)) k σ) := by
      refine ((h g₀).div_const c).congr fun x => ?_
      rw [classMomentTerm_fibre g₀ hc]
      field_simp
    exact (summable_twistMomentTerm_iff hBg (fun i hi => hW i g₀ hi) ⟨i₀, hne, hre⟩
      (fun i j hi hj hz _ => hinj i j (left_ne_zero_of_mul hi) (left_ne_zero_of_mul hj) hz)
      hk σ).mp hs
  · intro hσ g
    obtain ⟨c, hc, G, hG, hF⟩ := hB.chebotarev g
    have hBg := isAbelianBase_fibre hB g hc hG hF
    have hs := summable_twistMomentTerm hBg (z := z) (b := fun i => b i * φ i g)
      (fun _ => (1 : PUnit)) (fun i hi => hW i g hi) k hσ
    refine (hs.mul_left c).congr fun x => ?_
    rw [classMomentTerm_fibre g hc]

/-! ### The residue classes mod `q` -/

section Residue

open ArithmeticFunction

variable (q : ℕ) [NeZero q]

/-- The Frobenius class of `n` in `(ℤ/q)ˣ`; off the units, where the weight vanishes, it is `1`. -/
def residueFrob (n : ℕ) : (ZMod q)ˣ := if h : IsUnit (n : ZMod q) then h.unit else 1

/-- The von Mangoldt weight on the integers prime to `q`. -/
def residueLam (n : ℕ) : ℝ := if IsUnit (n : ZMod q) then Λ n else 0

theorem residueLam_nonneg (n : ℕ) : 0 ≤ residueLam q n := by
  unfold residueLam
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

/-- The series of the class `a` is the `L`-series of `Λ` on the progression `n ≡ a`. -/
theorem residue_fibre_tsum (a : (ZMod q)ˣ) (s : ℂ) :
    ∑' x : {n // residueFrob q n = a}, (residueLam q x : ℂ) * ((dirichletNorm x : ℝ) : ℂ) ^ (-s) =
      LSeries ↗(vonMangoldt.residueClass (a : ZMod q)) s := by
  rw [LSeries]
  refine (tsum_subtype {n | residueFrob q n = a}
    fun n => (residueLam q n : ℂ) * ((dirichletNorm n : ℝ) : ℂ) ^ (-s)).trans ?_
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, residueLam, Set.indicator_apply]
  · rw [LSeries.term_of_ne_zero hn, dirichletNorm,
      max_eq_left (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn), Complex.ofReal_natCast,
      Complex.cpow_neg, div_eq_mul_inv]
    by_cases hu : IsUnit (n : ZMod q)
    · have hiff : residueFrob q n = a ↔ (n : ZMod q) = a := by
        rw [residueFrob, dif_pos hu]
        exact ⟨fun h => by rw [← h]; rfl, fun h => Units.ext h⟩
      by_cases hna : (n : ZMod q) = a
      · simp [Set.indicator_apply, hiff.mpr hna, hna, residueLam, hu]
      · simp [Set.indicator_apply, mt hiff.mp hna, hna]
    · have hna : (n : ZMod q) ≠ a := fun h => hu (h ▸ a.isUnit)
      simp [Set.indicator_apply, residueLam, hu, hna]

/-- **Chebotarev for `ℚ(μ_q)`**: every class `a` has density `1/φ(q)`. -/
theorem residue_chebotarev (a : (ZMod q)ˣ) :
    ∃ c : ℝ, 0 < c ∧ ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      ∑' x : {n // residueFrob q n = a}, (residueLam q x : ℂ) * ((dirichletNorm x : ℝ) : ℂ) ^ (-s) =
        G s + (c : ℂ) / (s - 1) := by
  refine ⟨(q.totient : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)),
    vonMangoldt.LFunctionResidueClassAux (a : ZMod q),
    vonMangoldt.continuousOn_LFunctionResidueClassAux _, fun s hs => ?_⟩
  rw [residue_fibre_tsum, vonMangoldt.eqOn_LFunctionResidueClassAux a.isUnit (Set.mem_setOf.mpr hs)]
  push_cast
  ring

/-- **The residue classes mod `q` form a base with finite monodromy** `(ℤ/q)ˣ`. -/
theorem isFiniteMonodromyBase_residue :
    IsFiniteMonodromyBase dirichletNorm (residueLam q) (residueFrob q) where
  one_le_norm _ := le_max_right _ _
  lam_nonneg := residueLam_nonneg q
  summable_lam σ hσ := (summable_dirichletLam hσ).of_nonneg_of_le
    (fun n => mul_nonneg (residueLam_nonneg q n) (Real.rpow_nonneg (by
      exact le_trans zero_le_one (le_max_right _ _)) _))
    (fun n => by
      unfold residueLam
      split_ifs
      · exact le_rfl
      · simp only [zero_mul]
        exact mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (by
          exact le_trans zero_le_one (le_max_right _ _)) _))
  chebotarev := residue_chebotarev q

end Residue

end GaloisForLFunctions.TensorPowerProgramme
