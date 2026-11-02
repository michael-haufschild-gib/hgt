import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.SuccessorShellArithmetic.TheShellsAndThePoleCancelOnTheTopBand
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.CoprimeSuccessorGap
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimePoleNorm
import Mathlib.Data.Nat.Prime.Factorial


/-!
# Prime successors control nonconstant conductor packets

At a sufficiently large fixed overlap, the actual non-ratio matrix assigns weight at least
`log p / (2 N)` to each edge `(n, pn + 1)` with `N/2 < pn` and `pn + 1 ≤ N`.
For primes `Q < p ≤ N/(16 Q²)`, a window of length `N/(4p)` samples the coprime-successor
gap of every conductor packet through `Q`. Distinct prime-successor pairs give distinct
ordered edges, so their energies sum inside the affine Dirichlet form.

The resulting lower bound is uniform in the horizon, conductor and coefficient family:
`½ affineDirichlet ≥ (primePoleScale (N/(16 Q²)) - primePoleScale Q) * mass / 64`.
-/

open Finset MeasureTheory Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry ArithmeticElectrostatics
  ArithmeticEffectivityTheory CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory CriticalScaleArithmeticRigidity

/-- Small logarithmic lags retain half the atom mass, uniformly in the horizon. -/
private theorem exists_overlap_correlation_floor {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, C ≤ c → ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      |t| ≤ 2 / (N : ℝ) →
      (∫ u, atomDilate φ (c/N) u ^ 2) / 2 ≤ bumpCorr (atomDilate φ (c/N)) t := by
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  have hc := (continuous_bumpCorr hφ hcs).continuousAt (x := 0)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hc ((∫ u, φ u ^ 2)/2) (by positivity)
  refine ⟨4/δ, by positivity, fun c hc N hN t ht => ?_⟩
  have hc0 : 0 < c := (div_pos (by norm_num) hδ).trans_le hc
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c/(N:ℝ) := div_pos hc0 hN0
  have hδc : 4 ≤ δ*c := by
    have h := (div_le_iff₀ hδ).mp hc
    linarith only [h]
  have hsmall : |t/(c/N)| < δ := by
    rw [abs_div, abs_of_pos hw, div_lt_iff₀ hw]
    have htwo : 2/(N:ℝ) < δ*(c/N) := by
      simpa only [mul_div_assoc] using
        (div_lt_div_iff_of_pos_right hN0).mpr (show (2:ℝ) < δ*c by linarith only [hδc])
    exact ht.trans_lt htwo
  have hb := hnear (by simpa only [Real.dist_eq, sub_zero] using hsmall)
  rw [Real.dist_eq, bumpCorr_zero] at hb
  have hlow : (∫ u, φ u ^ 2)/2 ≤ bumpCorr φ (t/(c/N)) := by
    have h := (abs_lt.mp hb).1
    linarith only [h]
  have hd : bumpCorr (atomDilate φ (c/N)) t = (c/N) * bumpCorr φ (t/(c/N)) :=
    SuccessorShellArithmetic.bumpCorr_atomDilate_eq hw t
  rw [hd, integral_atomDilate_sq hw]
  nlinarith only [mul_le_mul_of_nonneg_left hlow hw.le]

/-- A successor edge above half the horizon has logarithmic lag at most `2/N`. -/
private theorem successor_log_lag_bound {N p n : ℕ} (hN : 1 ≤ N)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hpn : N < 2*p*n) :
    |Real.log p - (Real.log (p*n+1) - Real.log n)| ≤ 2/(N:ℝ) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < (p:ℝ)*n := mul_pos hp0 hn0
  have he : Real.log p - (Real.log (p*n+1) - Real.log n) =
      -Real.log (1 + 1/((p:ℝ)*n)) := by
    calc
      _ = Real.log ((p:ℝ)*n) - Real.log ((p:ℝ)*n+1) := by
        rw [Real.log_mul hp0.ne' hn0.ne']; ring
      _ = -Real.log (((p:ℝ)*n+1)/((p:ℝ)*n)) := by
        rw [Real.log_div (by positivity) hx.ne']; ring
      _ = _ := by congr 2; field_simp
  rw [he, abs_neg, abs_of_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity)))]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + 1/((p:ℝ)*n) by positivity)
  have hb : 1/((p:ℝ)*n) ≤ 2/(N:ℝ) := by
    rw [div_le_div_iff₀ hx hN0]
    have h := (show (N:ℝ) < 2*p*n by exact_mod_cast hpn)
    linarith only [h]
  linarith only [hlog, hb]

/-- The prime shift survives the exact-ratio subtraction on a successor edge. -/
private theorem nonRatioWeight_successor_ge {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ u, 0 ≤ φ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N p : ℕ}
    (i j : PrimeHorizonIndex N) (hp : p.Prime) (hi : 2 ≤ i.val)
    (hj : j.val = p*i.val+1) (hpn : N < 2*p*i.val)
    (hfloor : ∀ t : ℝ, |t| ≤ 2/(N:ℝ) →
      (∫ u, atomDilate φ (c/N) u ^ 2)/2 ≤ bumpCorr (atomDilate φ (c/N)) t) :
    Real.log p/(2*(N:ℝ)) ≤ nonRatioWeight φ c N i j := by
  have hiN := mem_Icc.mp i.property
  have hjN := mem_Icc.mp j.property
  have hN : 1 ≤ N := hiN.1.trans hiN.2
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : (0:ℝ) < i.val := by exact_mod_cast hiN.1
  have hj0 : (0:ℝ) < j.val := by exact_mod_cast hjN.1
  have hpN : p ≤ N := by nlinarith only [hj, hjN.2, hi, hp.two_le]
  have hndiv : ¬i.val ∣ j.val := by
    intro hd
    rw [hj] at hd
    have h1 : i.val ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_left i.val p)).mpr hd
    have := Nat.dvd_one.mp h1
    omega
  have hjdiv : ¬j.val ∣ i.val := by
    intro hd
    have hle := Nat.le_of_dvd (by omega : 0 < i.val) hd
    nlinarith only [hle, hj, hi, hp.two_le]
  have hkernel : weilPrimeKernel i j = 0 := by
    simp only [weilPrimeKernel, hndiv, hjdiv, false_and, if_false]
  have hw : 0 < c/(N:ℝ) := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  let g := atomDilate φ (c/N)
  let G := ∫ u, g u ^ 2
  have hG : 0 < G := by
    dsimp only [G, g]
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hg0 : ∀ u, 0 ≤ g u := fun u => hφ0 _
  let R := Real.log N + c/N + 1
  have hpR : p ∈ range (lagRange R) := by
    by_contra h
    have hlarge := two_mul_lt_abs_log_of_lagRange_le
      (show lagRange R ≤ p by simpa only [mem_range, not_lt] using h)
    rw [abs_of_nonneg (Real.log_natCast_nonneg p)] at hlarge
    have hlog := Real.log_le_log hp0 (show (p:ℝ) ≤ N by exact_mod_cast hpN)
    dsimp only [R] at hlarge
    linarith only [hlarge, hlog, Real.log_natCast_nonneg N, hw]
  have hplus (k : ℕ) : 0 ≤ ∫ u, atom g i u * atom g j (u + Real.log k) :=
    integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
  have hminus (k : ℕ) : 0 ≤ ∫ u, atom g i u * atom g j (u - Real.log k) :=
    integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
  -- Keep one positive prime shift in the finite prime-pair sum.
  have hpair : RHTower.vonMangoldtAtom p *
      bumpCorr g (Real.log p - (Real.log j.val - Real.log i.val)) ≤
      primePair (atom g i) (atom g j) := by
    rw [primePair_eq_sum_of_supportedIn (supportedIn_atom hgsupp hw.le i.property)
      (supportedIn_atom hgsupp hw.le j.property), ← integral_atom_mul_atom_add_log]
    apply (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hminus p))
      (RHTower.vonMangoldtAtom_nonneg' p)).trans
    exact single_le_sum (fun k _ => mul_nonneg (RHTower.vonMangoldtAtom_nonneg' k)
      (add_nonneg (hminus k) (hplus k))) hpR
  have hcorr : G/2 ≤ bumpCorr g (Real.log p - (Real.log j.val - Real.log i.val)) := by
    apply hfloor
    rw [hj]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
      successor_log_lag_bound hN hp.pos hiN.1 hpn
  have hv : RHTower.vonMangoldtAtom p = Real.log p / Real.sqrt p := by
    simp only [RHTower.vonMangoldtAtom, if_pos hp.two_le,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hentry : (Real.log p / Real.sqrt p)/2 ≤ fullWeilNonRatioMatrix φ c N i j := by
    rw [fullWeilNonRatioMatrix_apply, hkernel, sub_zero]
    change _ ≤ primePair (atom g i) (atom g j)/G
    apply (le_div_iff₀ hG).mpr
    have h := mul_le_mul_of_nonneg_left hcorr (RHTower.vonMangoldtAtom_nonneg' p)
    rw [hv] at h hpair
    nlinarith only [h, hpair]
  -- The square-root normalization is bounded by the endpoint, hence by the horizon.
  have hsqrt : Real.sqrt p * Real.sqrt i.val * Real.sqrt j.val ≤ (N:ℝ) := by
    have hpij : (p:ℝ)*i.val ≤ j.val := by exact_mod_cast (by omega : p*i.val ≤ j.val)
    have h := Real.sqrt_le_sqrt hpij
    rw [Real.sqrt_mul hp0.le] at h
    have hm := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg j.val)
    rw [Real.mul_self_sqrt hj0.le] at hm
    exact hm.trans (by exact_mod_cast hjN.2)
  rw [nonRatioWeight]
  calc
    _ ≤ Real.log p / (2*(Real.sqrt p * Real.sqrt i.val * Real.sqrt j.val)) :=
      div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)
        (by linarith only [hsqrt])
    _ = ((Real.log p / Real.sqrt p)/2) / (Real.sqrt i.val * Real.sqrt j.val) := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hentry (by positivity)

/-- The prime cutoff leaves a window longer than the conductor sampling error. -/
private theorem successor_window_size {N Q p : ℕ} (hQ : 2 ≤ Q) (hp : 1 ≤ p)
    (hcut : p ≤ N/(16*Q^2)) :
    4*Q^2 ≤ N/(4*p) ∧ 8*Q^2 ≤ N/(2*p) ∧ 4 ≤ N := by
  have hQ0 : 0 < 16*Q^2 := by positivity
  have hN := (Nat.le_div_iff_mul_le hQ0).mp hcut
  refine ⟨?_,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le (by positivity : 0 < 4*p)).mpr
    nlinarith only [hN]
  · apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2*p)).mpr
    nlinarith only [hN]
  · nlinarith only [hN, hQ, hp]

/-- Every retained successor edge lies inside the horizon and above its midpoint. -/
private theorem successor_window_bounds {N Q p n : ℕ} (hQ : 2 ≤ Q) (hp : 2 ≤ p)
    (hcut : p ≤ N/(16*Q^2))
    (hn : n ∈ Icc (N/(2*p)+1) (N/(2*p)+N/(4*p))) :
    2 ≤ n ∧ p*n+1 ≤ N ∧ N < 2*p*n := by
  obtain ⟨hK,hA,hN⟩ := successor_window_size hQ (by omega) hcut
  obtain ⟨hnlo,hnhi⟩ := mem_Icc.mp hn
  have h1 := Nat.div_mul_le_self N (2*p)
  have h2 := Nat.div_mul_le_self N (4*p)
  have hpn := Nat.mul_le_mul_right p hnhi
  have hlow : N < n*(2*p) :=
    (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2*p)).mp (by omega)
  refine ⟨?_,?_,by nlinarith only [hlow]⟩
  · nlinarith only [hnlo, hA, hQ]
  · nlinarith only [h1, h2, hpn, hN]

/-- The coprime-successor gap pays `N/(16p)` times the nonconstant coefficient mass. -/
private theorem successor_window_mass {N Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime)
    (hQp : Q < p) (hcut : p ≤ N/(16*Q^2)) (a : ℕ → ℝ) :
    ((N:ℝ)/(16*p)) * nonconstantPacketMass Q a ≤
      ∑ n ∈ Icc (N/(2*p)+1) (N/(2*p)+N/(4*p)),
        (conductorPacket Q a (p*n+1) - conductorPacket Q a n)^2 := by
  obtain ⟨hK,_,_⟩ := successor_window_size hQ hp.pos hcut
  have hKreal : 4*(Q:ℝ)^2 ≤ (N/(4*p) : ℕ) := by exact_mod_cast hK
  have hQreal : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hppos : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hK1 : 1 ≤ N/(4*p) := by nlinarith only [hK, hQ]
  have hpNat : 0 < p := hp.pos
  have hdiv := Nat.lt_mul_div_succ N (by positivity : 0 < 4*p)
  have hdivreal : (N:ℝ) < 4*p*((N/(4*p):ℕ)+1) := by exact_mod_cast hdiv
  have hKreal1 : (1:ℝ) ≤ (N/(4*p):ℕ) := by exact_mod_cast hK1
  have hcoef : (N:ℝ)/(16*p) ≤ (N/(4*p):ℕ) - (Q:ℝ)*((Q:ℝ)-1) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 16*p)).mpr
    have hdiff : 0 ≤ (N/(4*p):ℕ) - 2*(Q:ℝ)*((Q:ℝ)-1) := by
      nlinarith only [hKreal, hQreal]
    have hmul := mul_nonneg hppos.le hdiff
    have hmul1 := mul_nonneg hppos.le (sub_nonneg.mpr hKreal1)
    nlinarith only [hdivreal, hmul, hmul1]
  have hcop : Nat.Coprime Q.factorial p := (hp.coprime_factorial_of_lt hQp).symm
  have hwindow := coprime_successor_window_lower hQ hcop a (N/(2*p)) (N/(4*p))
    (by nlinarith only [hKreal, hQreal])
  exact (mul_le_mul_of_nonneg_right hcoef (nonconstantPacketMass_nonneg Q a)).trans hwindow

/-- Primes preserving all conductor modes while leaving a long sampling window. -/
private def successorPrimes (Q N : ℕ) : Finset ℕ :=
  (Icc (Q+1) (N/(16*Q^2))).filter Nat.Prime

/-- Prime-labelled starting points of the retained successor edges. -/
private def successorChannels (Q N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (successorPrimes Q N).sigma (fun p => Icc (N/(2*p)+1) (N/(2*p)+N/(4*p)))

private theorem successorChannels_bounds {Q N : ℕ} (hQ : 2 ≤ Q)
    (x : ↥(successorChannels Q N)) :
    2 ≤ x.val.2 ∧ x.val.1*x.val.2+1 ≤ N ∧ N < 2*x.val.1*x.val.2 := by
  obtain ⟨hp,hn⟩ := mem_sigma.mp x.property
  obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
  exact successor_window_bounds hQ hpP.two_le (mem_Icc.mp hpI).2 hn

private def successorEdge {Q N : ℕ} (hQ : 2 ≤ Q)
    (x : ↥(successorChannels Q N)) : PrimeHorizonIndex N × PrimeHorizonIndex N :=
  let h := successorChannels_bounds hQ x
  ⟨⟨x.val.2, mem_Icc.mpr ⟨by omega, by
      obtain ⟨hp,_⟩ := mem_sigma.mp x.property
      have hpP := (mem_filter.mp hp).2
      nlinarith only [h.2.1, hpP.two_le, h.1]⟩⟩,
    ⟨x.val.1*x.val.2+1, mem_Icc.mpr ⟨by omega,h.2.1⟩⟩⟩

/-- The ordered edge determines its positive starting point and its prime multiplier. -/
private theorem successorEdge_injective {Q N : ℕ} (hQ : 2 ≤ Q) :
    Function.Injective (successorEdge (N := N) hQ) := by
  intro x y h
  have hn := congrArg (fun z : PrimeHorizonIndex N × PrimeHorizonIndex N => z.1.val) h
  have hm := congrArg (fun z : PrimeHorizonIndex N × PrimeHorizonIndex N => z.2.val) h
  change x.val.2 = y.val.2 at hn
  change x.val.1*x.val.2+1 = y.val.1*y.val.2+1 at hm
  have hpos : 0 < y.val.2 := by have hy := (successorChannels_bounds hQ y).1; omega
  have hp : x.val.1 = y.val.1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hn] at hm
    omega
  apply Subtype.ext
  exact Sigma.ext hp (heq_of_eq hn)

/-- The selected edges contribute disjoint nonnegative summands to the actual energy. -/
private theorem successor_edge_sum_le_affine {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ u, 0 ≤ φ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N Q : ℕ} (hQ : 2 ≤ Q)
    (hfloor : ∀ t : ℝ, |t| ≤ 2/(N:ℝ) →
      (∫ u, atomDilate φ (c/N) u ^ 2)/2 ≤ bumpCorr (atomDilate φ (c/N)) t)
    (F : ℕ → ℝ) :
    ∑ p ∈ successorPrimes Q N, Real.log p/(2*(N:ℝ)) *
      ∑ n ∈ Icc (N/(2*p)+1) (N/(2*p)+N/(4*p)), (F (p*n+1)-F n)^2 ≤
      affineDirichlet φ c N F := by
  let V : (PrimeHorizonIndex N × PrimeHorizonIndex N) → ℝ := fun z =>
    nonRatioWeight φ c N z.1 z.2 * (F z.1.val-F z.2.val)^2
  have hV (z : PrimeHorizonIndex N × PrimeHorizonIndex N) : 0 ≤ V z :=
    mul_nonneg (nonRatioWeight_nonneg hφ0 hsupp hM hc _ _) (sq_nonneg _)
  -- Inject the selected channels into the ordered horizon pairs.
  have hsub : ∑ x : ↥(successorChannels Q N), V (successorEdge hQ x) ≤
      ∑ z : PrimeHorizonIndex N × PrimeHorizonIndex N, V z := by
    calc
      _ = ∑ z ∈ univ.image (successorEdge (N := N) hQ), V z :=
        (sum_image (fun _ _ _ _ he => successorEdge_injective hQ he)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z _ _ => hV z)
  have hweights : ∑ x : ↥(successorChannels Q N),
      Real.log x.val.1/(2*(N:ℝ)) * (F (x.val.1*x.val.2+1)-F x.val.2)^2 ≤
      ∑ x : ↥(successorChannels Q N), V (successorEdge hQ x) := by
    apply sum_le_sum
    intro x _
    obtain ⟨hp,_⟩ := mem_sigma.mp x.property
    have hpP := (mem_filter.mp hp).2
    have hx := successorChannels_bounds hQ x
    have hw := nonRatioWeight_successor_ge hφ hφ0 hsupp hM hc
      (successorEdge hQ x).1 (successorEdge hQ x).2 hpP hx.1 rfl hx.2.2 hfloor
    have hm := mul_le_mul_of_nonneg_right hw (sq_nonneg (F x.val.2-F (x.val.1*x.val.2+1)))
    change _ ≤ nonRatioWeight φ c N (successorEdge hQ x).1 (successorEdge hQ x).2 *
      (F x.val.2-F (x.val.1*x.val.2+1))^2
    nlinarith only [hm]
  have he : (∑ x : ↥(successorChannels Q N),
      Real.log x.val.1/(2*(N:ℝ)) * (F (x.val.1*x.val.2+1)-F x.val.2)^2) =
      ∑ p ∈ successorPrimes Q N, Real.log p/(2*(N:ℝ)) *
        ∑ n ∈ Icc (N/(2*p)+1) (N/(2*p)+N/(4*p)), (F (p*n+1)-F n)^2 := by
    have hcoe := sum_coe_sort (successorChannels Q N)
      (fun x : Σ _ : ℕ, ℕ => Real.log x.1/(2*(N:ℝ)) * (F (x.1*x.2+1)-F x.2)^2)
    rw [hcoe, successorChannels, sum_sigma]
    apply sum_congr rfl
    intro p _
    rw [mul_sum]
  rw [← he]
  have hfull : (∑ z : PrimeHorizonIndex N × PrimeHorizonIndex N, V z) =
      affineDirichlet φ c N F := by rw [Fintype.sum_prod_type]; rfl
  exact (hweights.trans hsub).trans_eq hfull

/-- Summing the window gaps gives a prime-weighted bound for all packet coefficients. -/
private theorem affine_prime_successor_mass_lower {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ u, 0 ≤ φ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N Q : ℕ}
    (hN : 1 ≤ N) (hQ : 2 ≤ Q)
    (hfloor : ∀ t : ℝ, |t| ≤ 2/(N:ℝ) →
      (∫ u, atomDilate φ (c/N) u ^ 2)/2 ≤ bumpCorr (atomDilate φ (c/N)) t)
    (a : ℕ → ℝ) :
    (∑ p ∈ successorPrimes Q N, Real.log p/(p:ℝ))/32 * nonconstantPacketMass Q a ≤
      affineDirichlet φ c N (conductorPacket Q a) := by
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hterm : ∀ p ∈ successorPrimes Q N,
      (Real.log p/(p:ℝ))/32 * nonconstantPacketMass Q a ≤
        Real.log p/(2*(N:ℝ)) *
          ∑ n ∈ Icc (N/(2*p)+1) (N/(2*p)+N/(4*p)),
            (conductorPacket Q a (p*n+1)-conductorPacket Q a n)^2 := by
    intro p hp
    obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
    have hpB := mem_Icc.mp hpI
    have h := mul_le_mul_of_nonneg_left
      (successor_window_mass hQ hpP (by omega) hpB.2 a)
      (show 0 ≤ Real.log p/(2*(N:ℝ)) by positivity)
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hpP.ne_zero
    calc
      _ = Real.log p/(2*(N:ℝ)) * (((N:ℝ)/(16*p)) * nonconstantPacketMass Q a) := by
        field_simp [hN0, hp0]
        ring
      _ ≤ _ := h
  have he : (∑ p ∈ successorPrimes Q N, Real.log p/(p:ℝ))/32 * nonconstantPacketMass Q a =
      ∑ p ∈ successorPrimes Q N, (Real.log p/(p:ℝ))/32 * nonconstantPacketMass Q a := by
    rw [sum_div, sum_mul]
  rw [he]
  exact (sum_le_sum hterm).trans
    (successor_edge_sum_le_affine hφ hφ0 hsupp hM hc hQ hfloor (conductorPacket Q a))

/-- Prime successors supply a uniform lower bound on every nonconstant packet coefficient.
The prime cutoff leaves a sampling window of length at least four times the conductor squared. -/
theorem prime_successor_edges_control_nonconstant_packets_in_range {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, C ≤ c → ∀ N : ℕ, 1 ≤ N → ∀ Q : ℕ, 2 ≤ Q →
      ∀ a : ℕ → ℝ,
      (∑ p ∈ (Icc (Q+1) (N/(16*Q^2))).filter Nat.Prime, Real.log p/(p:ℝ))/32 *
        nonconstantPacketMass Q a ≤ affineDirichlet φ c N (conductorPacket Q a) := by
  obtain ⟨C,hC,hfloor⟩ := exists_overlap_correlation_floor hφ hsupp hM
  refine ⟨C,hC,fun c hc N hN Q hQ a => ?_⟩
  exact affine_prime_successor_mass_lower hφ hφ0 hsupp hM (hC.trans_le hc) hN hQ
    (hfloor c hc N hN) a

/-- The prime-scale difference is bounded by the retained sum even when the interval is empty. -/
private theorem primePoleScale_sub_le_successor_sum (Q M : ℕ) :
    primePoleScale M - primePoleScale Q ≤
      ∑ p ∈ (Icc (Q+1) M).filter Nat.Prime, Real.log p/(p:ℝ) := by
  have hd : Disjoint ((Icc 1 Q).filter Nat.Prime) ((Icc (Q+1) M).filter Nat.Prime) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := mem_Icc.mp (mem_filter.mp hp).1
    have hq' := mem_Icc.mp (mem_filter.mp hq).1
    omega
  have hs : (Icc 1 M).filter Nat.Prime ⊆
      ((Icc 1 Q).filter Nat.Prime) ∪ ((Icc (Q+1) M).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
    obtain ⟨hp1,hpM⟩ := mem_Icc.mp hpI
    by_cases hpQ : p ≤ Q
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp1,hpQ⟩,hpP⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hpM⟩,hpP⟩)
  have h := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log p/(p:ℝ)) hs
    (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  rw [sum_union hd] at h
  change primePoleScale M ≤ primePoleScale Q + _ at h
  linarith only [h]

/-- The actual affine Dirichlet term pays the prime-pole scale between the conductor and
`N / (16 Q²)`, uniformly over packet coefficients once the overlap is large enough. -/
theorem prime_successor_edges_control_nonconstant_packets {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, C ≤ c → ∀ N : ℕ, 1 ≤ N → ∀ Q : ℕ, 2 ≤ Q →
      ∀ a : ℕ → ℝ,
      (1/64:ℝ) * (primePoleScale (N/(16*Q^2)) - primePoleScale Q) *
        nonconstantPacketMass Q a ≤ (1/2:ℝ) * affineDirichlet φ c N (conductorPacket Q a) := by
  obtain ⟨C,hC,hbound⟩ := prime_successor_edges_control_nonconstant_packets_in_range
    hφ hφ0 hsupp hM
  refine ⟨C,hC,fun c hc N hN Q hQ a => ?_⟩
  have h := hbound c hc N hN Q hQ a
  have hscale := mul_le_mul_of_nonneg_right (primePoleScale_sub_le_successor_sum Q (N/(16*Q^2)))
    (nonconstantPacketMass_nonneg Q a)
  nlinarith only [h, hscale]

#print axioms prime_successor_edges_control_nonconstant_packets_in_range
#print axioms prime_successor_edges_control_nonconstant_packets

end GaloisForLFunctions.ArithmeticCouplingTheory
