import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeIsACrossing
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheKahlerPackage
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsAreLowerHorizons
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.InfiniteGenusLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochAwayFromTheLowFrequencyDivisor
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapGramSmoothingNeedsAQuarterDefectCorrection

/-!
# The Liouville property of the Weil operator

A **harmonic packet** of a form that is `≥ 0` on the primitive part is a primitive vector in its
radical, i.e. a zero mode on `v₁^⊥`. The **Liouville property** asks that harmonic packets have
vanishing dilation-jump energy.

* **Liouville for the dilation Laplacian** (`eq_of_dilationEnergy_eq_zero`,
  `eq_zero_of_dilationEnergy_eq_zero_of_primitive`, `eq_zero_of_poleDefect_eq_zero_of_primitive`).
  Every `n ≤ N` is reached from `1` by prime dilations, so a packet of zero dilation energy is
  constant. A primitive constant packet is zero.
* **Liouville is hard Lefschetz** (`liouvilleAt_iff_hardLefschetz`). Since the kernel of the jump
  energy meets the primitive part only in `0`, the Liouville property at a resolution is exactly
  nondegeneracy of the hyperplane form, i.e. hard Lefschetz.
* **Transport** (`hyperplanePositiveAt_of_liouville`). Along the overlap flow, hard Lefschetz is
  needed only where Hodge–Riemann already holds: from a base overlap where the hyperplane form is
  positive, the Liouville property on the positive locus carries positivity through every overlap
  of the interval. This is the Kähler-package transport (`hodgeRiemann_transport_on`) applied to
  the continuous complete Weil family.
* **RH is the Liouville property along the overlap flow**
  (`riemannHypothesis_iff_liouville_along_the_overlap_flow`). Under RH Weil's form is positive
  definite on nonzero tests, so the complete Weil matrix has no zero modes at all
  (`completeWeilEnergy_pos_of_riemannHypothesis`). Conversely, the universal regime supplies the
  base point at overlap `1`, and the Liouville property up to `2(log N)^β`, `β > 1/2`, transports
  the hyperplane positivity to the RH receiver of RIT.

So the Liouville test of the review is not softer than RH: the deformation mechanism itself is
exact and costs nothing, and the entire content sits in the nondegeneracy of the form on the
positive locus.
-/

noncomputable section

open Finset Filter Topology Matrix
open scoped RealInnerProductSpace
open GaloisForLFunctions.ArithmeticCouplingTheory GaloisForLFunctions.ArithmeticLorentzianGeometry
  GaloisForLFunctions.EdgeHodgeTheory GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

open GaloisForLFunctions.CriticalArithmeticCorrelationTheory
  (eventually_tiltedUnitSpline_completeWeilMatrix_posDef_powerLog powerLogPositivityExponent
    powerLogPositivityExponent_pos)

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-! ### Liouville for the dilation Laplacian -/

/-- **Dilation-harmonic packets are constant.** For a weight that is nonnegative and positive on
primes, zero dilation energy forces `F(n) = F(1)` on `[1, N]`. -/
theorem eq_of_dilationEnergy_eq_zero {lam : ℕ → ℝ} (hnn : ∀ k, 0 ≤ lam k)
    (hpos : ∀ p, p.Prime → 0 < lam p) {N : ℕ} {F : ℕ → ℝ} (h : dilationEnergy lam N F = 0) :
    ∀ n ∈ Icc 1 N, F n = F 1 := by
  have hterm : ∀ q ∈ dilationPairs N,
      lam q.1 / q.1 * ((F (q.1 * q.2) - F q.2) ^ 2 / q.2) = 0 :=
    (sum_eq_zero_iff_of_nonneg fun q _ => mul_nonneg (div_nonneg (hnn _) (Nat.cast_nonneg _))
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))).mp h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  rcases eq_or_lt_of_le hn1 with rfl | hn2
  · rfl
  · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp at hm; omega
      · exact h0
    have hmn : m < n := by rw [hm]; nlinarith [hp.two_le]
    have hmem : (n.minFac, m) ∈ dilationPairs N :=
      mem_dilationPairs.mpr ⟨hp.one_lt.le, hm1, hm ▸ hnN⟩
    have h0 := hterm _ hmem
    have hlp : lam n.minFac / n.minFac ≠ 0 :=
      (div_pos (hpos _ hp) (by exact_mod_cast hp.pos)).ne'
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    simp only [mul_eq_zero, hlp, false_or, div_eq_zero_iff, hm0, or_false,
      pow_eq_zero_iff two_ne_zero, sub_eq_zero] at h0
    rw [hm, h0]
    exact ih m hmn (mem_Icc.mpr ⟨hm1, by omega⟩)

/-- **Primitive dilation-harmonic packets vanish**: a packet with `Σ F(n)/n = 0` and zero dilation
energy is zero on `[1, N]`. -/
theorem eq_zero_of_dilationEnergy_eq_zero_of_primitive {lam : ℕ → ℝ} (hnn : ∀ k, 0 ≤ lam k)
    (hpos : ∀ p, p.Prime → 0 < lam p) {N : ℕ} (hN : 1 ≤ N) {F : ℕ → ℝ}
    (hprim : ∑ n ∈ Icc 1 N, F n / n = 0) (h : dilationEnergy lam N F = 0) :
    ∀ n ∈ Icc 1 N, F n = 0 := by
  have hconst := eq_of_dilationEnergy_eq_zero hnn hpos h
  have hsum : ∑ n ∈ Icc 1 N, F n / n = F 1 * ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
    rw [mul_sum]
    exact sum_congr rfl fun n hn => by rw [hconst n hn]; ring
  have hH : 0 < ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
    sum_pos (fun n hn => by have := (mem_Icc.mp hn).1; positivity) ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  have hF1 : F 1 = 0 := by
    rw [hsum] at hprim
    exact (mul_eq_zero.mp hprim).resolve_right hH.ne'
  intro n hn
  rw [hconst n hn, hF1]

/-- **Liouville in Weil's coordinates.** A primitive vector of zero pole defect is zero
(`N ≥ 2`). -/
theorem eq_zero_of_poleDefect_eq_zero_of_primitive {N : ℕ} (hN : 2 ≤ N)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hprim : ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0)
    (h : poleDefect N (primeHorizonExtension x) = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := (poleDefect_eq_zero_iff_horizonPoleVector (by omega) x).mp h
  rw [RenormalizedIntersectionTheory.inner_normalizedRamanujanHorizonVector_one] at hprim
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hsum : ∑ n ∈ Icc 1 N, primeHorizonExtension (a • horizonPoleVector N) n / Real.sqrt n =
      a * ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [primeHorizonExtension, dif_pos hn, horizonPoleVector, horizonProfileVector,
      PiLp.smul_apply, smul_eq_mul]
    calc a * (1 / Real.sqrt n) / Real.sqrt n = a * (1 / (Real.sqrt n * Real.sqrt n)) := by ring
      _ = a * (1 / n) := by rw [Real.mul_self_sqrt hn0.le]
  have hH : 0 < ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
    sum_pos (fun n hn => by have := (mem_Icc.mp hn).1; positivity)
      ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  rw [hsum] at hprim
  have ha : a = 0 := by
    have hs : (Real.sqrt (Real.log N))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hlog).ne'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hprim).resolve_left hs)).resolve_right hH.ne'
  rw [ha, zero_smul]

/-! ### The complete Weil family as a Kähler package -/

/-- The pole class `v₁` of horizon `N`, as a function on the horizon. -/
def poleClass (N : ℕ) : PrimeHorizonIndex N → ℝ := fun n => normalizedRamanujanHorizonVector 1 N n

theorem completeWeilEnergy_eq_qf (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N x = qf (completeWeilMatrix φ c N) (fun n => x n) := by
  rw [completeWeilEnergy, EuclideanSpace.inner_eq_star_dotProduct, qf, bil]
  rfl

theorem inner_poleClass {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = (fun n => x n) ⬝ᵥ poleClass N := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

theorem completeWeilMatrix_isSymm (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (completeWeilMatrix φ c N).IsSymm := by
  have h := completeWeilMatrix_isHermitian φ c N
  ext i j
  simpa using (h.apply j i).symm

/-- **Hyperplane positivity is Hodge–Riemann** for the pole class. -/
theorem hyperplanePositiveAt_iff_hodgeRiemann {φ : ℝ → ℝ} {c : ℝ} {N : ℕ} :
    HyperplanePositiveAt φ c N ↔ HodgeRiemann (completeWeilMatrix φ c N) (poleClass N) := by
  constructor
  · intro h y hy
    have := h (WithLp.toLp 2 y) (by rw [inner_poleClass]; exact hy)
    rwa [completeWeilEnergy_eq_qf] at this
  · intro h x hx
    rw [completeWeilEnergy_eq_qf]
    exact h _ (by rw [← inner_poleClass]; exact hx)

/-- **The Liouville property at a resolution**: every primitive zero mode of the hyperplane form
has zero dilation-jump (pole) defect. -/
def LiouvilleAt (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : Prop :=
  ∀ x : PrimeHorizonIndex N → ℝ, x ⬝ᵥ poleClass N = 0 →
    (∀ y : PrimeHorizonIndex N → ℝ, y ⬝ᵥ poleClass N = 0 → bil (completeWeilMatrix φ c N) x y = 0) →
      poleDefect N (primeHorizonExtension (WithLp.toLp 2 x)) = 0

/-- **The Liouville property is hard Lefschetz** (`N ≥ 2`). -/
theorem liouvilleAt_iff_hardLefschetz {φ : ℝ → ℝ} {c : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    LiouvilleAt φ c N ↔ HardLefschetz (completeWeilMatrix φ c N) (poleClass N) := by
  constructor
  · intro h x hx hrad
    have h0 := eq_zero_of_poleDefect_eq_zero_of_primitive hN
      (by rw [inner_poleClass]; exact hx) (h x hx hrad)
    funext n
    exact congrFun (congrArg WithLp.ofLp h0) n
  · intro h x hx hrad
    rw [h x hx hrad]
    simp [poleDefect, primeHorizonExtension]

/-! ### Transport along the overlap flow -/

theorem continuousOn_completeWeilMatrix {φ : ℝ → ℝ} (hφ : Admissible φ) {N : ℕ} (hN : 1 ≤ N)
    {S : Set ℝ} (hS : ∀ c ∈ S, 0 < c) : ContinuousOn (fun c => completeWeilMatrix φ c N) S :=
  continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => fun c hc =>
    (continuousAt_completeWeilMatrix_apply hφ hN (hS c hc) i j).continuousWithinAt

/-- **Liouville transport.** From a base overlap `a > 0` where the hyperplane form is positive,
the Liouville property on the positive locus of `[a, b]` gives positivity on all of `[a, b]`. -/
theorem hyperplanePositiveAt_of_liouville {φ : ℝ → ℝ} (hφ : Admissible φ) {N : ℕ} (hN : 1 ≤ N)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbase : HyperplanePositiveAt φ a N)
    (hL : ∀ c ∈ Set.Icc a b, HyperplanePositiveAt φ c N →
      HardLefschetz (completeWeilMatrix φ c N) (poleClass N)) :
    ∀ c ∈ Set.Icc a b, HyperplanePositiveAt φ c N := by
  intro c hc
  rw [hyperplanePositiveAt_iff_hodgeRiemann]
  refine hodgeRiemann_transport_on isPreconnected_Icc
    (continuousOn_completeWeilMatrix hφ hN fun c hc => ha.trans_le hc.1)
    (fun c _ => completeWeilMatrix_isSymm φ c N) (poleClass N)
    (fun c hc h => hL c hc (hyperplanePositiveAt_iff_hodgeRiemann.mpr h))
    (Set.left_mem_Icc.mpr hab) (hyperplanePositiveAt_iff_hodgeRiemann.mp hbase) hc

/-! ### Under RH there are no zero modes -/

/-- **Atomic tests are faithful**: distinct translates of a nonzero compactly supported atom are
linearly independent, so a vanishing atomic test has zero coefficients. -/
theorem eq_zero_of_atomicTest_eq_zero {g : ℝ → ℝ} (hgc : HasCompactSupport g) (hg0 : g ≠ 0)
    {N : ℕ} {x : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (h : atomicTest N (primeHorizonExtension x) g = 0) : x = 0 := by
  have hinj : Function.Injective fun j : Fin N => Real.log (((j : ℕ) : ℝ) + 1) := by
    intro i j hij
    have hi : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
    have hj : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
    have := Real.log_injOn_pos hi hj hij
    exact Fin.ext (by exact_mod_cast (by linarith : ((i : ℕ) : ℝ) = (j : ℕ)))
  have hli := Fintype.linearIndependent_iff.mp
    (ArithmeticCastelnuovoSeveri.linearIndependent_real_translate hinj hgc hg0)
  have hsum : ∑ i : Fin N, x ((primeHorizonFinEquiv N).symm i) •
      (fun u => g (u - Real.log (((i : ℕ) : ℝ) + 1))) = 0 := by
    rw [← finAtomicTest_primeHorizonFinEquiv] at h
    funext u
    have hu := congrFun h u
    simp only [finAtomicTest, atom, Pi.zero_apply] at hu
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rfl
  ext n
  have := hli _ hsum (primeHorizonFinEquiv N n)
  simpa using this

/-- **Under RH Weil's form is positive on every nonzero `C²` compactly supported real test.** -/
theorem weilQuad_pos_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : f ≠ 0) : 0 < weilQuad f := by
  rw [ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW hf hfc]
  have hcomplex : ContDiff ℝ 2 (fun u => (f u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcompact : HasCompactSupport (fun u => (f u : ℂ)) := hfc.comp_left Complex.ofReal_zero
  exact ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_weil_positive_definite.mp hRH _
    hcomplex hcompact fun h => hf0 (funext fun u => by simpa using congrFun h u)

/-- **Under RH the complete Weil family is positive definite** at every resolution. -/
theorem completeWeilEnergy_pos_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : Admissible φ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : x ≠ 0) :
    0 < completeWeilEnergy φ c N x := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ.contDiff hφ.supp hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw hφ.sq_pos
  have hg0 : atomDilate φ (c / N) ≠ 0 := fun h0 => by
    have : (∫ u, atomDilate φ (c / N) u ^ 2) = 0 := by simp [h0]
    exact hG.ne' this
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ.contDiff hφ.supp hc hN]
  exact div_pos (weilQuad_pos_of_riemannHypothesis hRH (contDiff_atomicTest hg N _)
    (hasCompactSupport_atomicTest hgs N _) fun h => hx (eq_zero_of_atomicTest_eq_zero hgc hg0 h)) hG

/-- **Under RH the hyperplane form satisfies hard Lefschetz** at every resolution. -/
theorem hardLefschetz_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : Admissible φ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    HardLefschetz (completeWeilMatrix φ c N) (poleClass N) := by
  intro x hx hrad
  by_contra hx0
  have hx0' : (WithLp.toLp 2 x : EuclideanSpace ℝ (PrimeHorizonIndex N)) ≠ 0 := fun h =>
    hx0 (by funext n; exact congrFun (congrArg WithLp.ofLp h) n)
  have hpos := completeWeilEnergy_pos_of_riemannHypothesis hRH hφ hc hN hx0'
  rw [completeWeilEnergy_eq_qf] at hpos
  have : qf (completeWeilMatrix φ c N) x = 0 := hrad x hx
  exact absurd this (ne_of_gt (by simpa using hpos))

/-! ### RH is the Liouville property along the overlap flow -/

/-- **RH is the Liouville property along the overlap flow.** For `β > 1/2`: RH holds iff,
eventually in `N`, at every overlap `c ∈ [1, 2(log N)^β]` where the hyperplane form of the tilted
spline is positive, it is nondegenerate on the primitive part. -/
theorem riemannHypothesis_iff_liouville_along_the_overlap_flow {β : ℝ} (hβ : 1 / 2 < β) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ c ∈ Set.Icc 1 (2 * Real.log N ^ β),
      HyperplanePositiveAt tiltedUnitSpline c N →
        HardLefschetz (completeWeilMatrix tiltedUnitSpline c N) (poleClass N) := by
  constructor
  · intro hRH
    filter_upwards [eventually_ge_atTop 1] with N hN c hc _
    exact hardLefschetz_of_riemannHypothesis hRH admissible_tiltedUnitSpline
      (one_pos.trans_le hc.1) hN
  · intro H
    have hα := powerLogPositivityExponent_pos
    refine (RenormalizedIntersectionTheory.riemannHypothesis_iff_completeWeil_hodgeIndex_log
      hβ).mpr ?_
    have hlog1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    have hpd0 := eventually_tiltedUnitSpline_completeWeilMatrix_posDef_powerLog
      (α := powerLogPositivityExponent / 2) (by linarith) (by linarith)
    filter_upwards [H, hpd0, hlog1, eventually_one_le_two_mul_rpow_log (by linarith : (0 : ℝ) ≤ β),
      eventually_ge_atTop 1] with N hN hpd hlogN htop hN1
    have hbase : HyperplanePositiveAt tiltedUnitSpline 1 N := fun x _ =>
      RenormalizedIntersectionTheory.energy_nonneg_of_posDef (completeWeilMatrix_isHermitian _ _ _)
        (hpd 1 le_rfl (Real.one_le_rpow hlogN (by linarith))) x
    exact hyperplanePositiveAt_of_liouville admissible_tiltedUnitSpline hN1 one_pos htop hbase hN
      _ ⟨htop, le_rfl⟩

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
