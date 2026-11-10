import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticResidueProfiles
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrincipalProfileScaling

/-!
# The arithmetic correction to the principal prime profile

Finite character inversion separates the actual residue-class prime sum
into its principal mean and a regular correction. Nonprincipal character
logarithms extend through one; the ramified primes contribute exactly the
difference between their chosen profiles and that mean. Both corrections
vanish at the common endpoint.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
variable {q : ℕ} [NeZero q]

private theorem characterProfile_tube_mono {e d : ℝ} (hed : e ≤ d) :
    {s : ℂ | 1 - e < s.re ∧ |s.im| < e} ⊆ {s : ℂ | 1 - d < s.re ∧ |s.im| < d} := by
  intro s hs
  exact ⟨by linarith only [hs.1, hed], hs.2.trans_le hed⟩

/-- A finite nonprincipal character family has one common continuation tube. -/
private theorem exists_finite_characterProfile_continuation
    (P : DirichletCharacter ℂ q → ℂ → ℂ) {R : NNReal} (hR : 1 < (R : ℝ))
    (hP : ∀ χ, AnalyticOnNhd ℂ (P χ) (closedBall 0 R))
    (h1 : ∀ χ, χ ≠ 1 → P χ 1 = 1)
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ ≠ 1) :
    ∃ e : ℝ, 0 < e ∧ ∃ K : ℝ → ℂ → ℂ,
      (∀ t : ℝ, 0 ≤ t → AnalyticOnNhd ℂ (K t) {s | 1 - e < s.re ∧ |s.im| < e}) ∧
      ContinuousOn (fun v : ℝ × ℂ => K v.1 v.2)
        (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) ∧
      (∀ s : ℂ, K 0 s = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ s : ℂ, 1 < s.re →
        K t s = ∑ χ ∈ S, weightedProfilePrimeSum (fun p => χ p) (P χ) t s) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, zero_lt_one, fun _ _ => 0, fun _ _ => analyticOnNhd_const,
        continuousOn_const, fun _ => rfl, ?_⟩
      intro t ht s hs
      simp only [Finset.sum_empty]
  | @insert χ S hχS ih =>
      intro hS
      have hχ : χ ≠ 1 := hS χ (Finset.mem_insert_self χ S)
      obtain ⟨e, he, K, hKa, hKc, hK0, hKe⟩ :=
        exists_characterProfile_continuation hχ hR (hP χ) (h1 χ hχ)
      obtain ⟨d, hd, L, hLa, hLc, hL0, hLe⟩ :=
        ih (fun ψ hψ => hS ψ (Finset.mem_insert_of_mem hψ))
      have hsube := characterProfile_tube_mono (min_le_left e d)
      have hsubd := characterProfile_tube_mono (min_le_right e d)
      refine ⟨min e d, lt_min he hd, fun t s => K t s + L t s,
        fun t ht => ((hKa t ht).mono hsube).add ((hLa t ht).mono hsubd),
        (hKc.mono (fun v hv => ⟨hv.1, hsube hv.2⟩)).add
          (hLc.mono (fun v hv => ⟨hv.1, hsubd hv.2⟩)), ?_, ?_⟩
      · intro s
        rw [hK0 s, hL0 s, add_zero]
      · intro t ht s hs
        rw [hKe t ht s hs, hLe t ht s hs, Finset.sum_insert hχS]

/-- The ramified correction replaces the mean by the actual chosen profile. -/
def residueFiniteCorrection (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (t : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ residueRamifiedPrimes q,
    (analyticSmoothingPrimePhase (ρ p) p (t : ℂ) -
      analyticSmoothingPrimePhase (residueAverage Φ) p (t : ℂ)) * ((p : ℕ) : ℂ) ^ (-s)

theorem residueFiniteCorrection_zero {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (h1 : residueAverage Φ 1 = -1) (hρ1 : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ρ p 1 = -1) (s : ℂ) :
    residueFiniteCorrection Φ ρ 0 s = 0 := by
  unfold residueFiniteCorrection
  apply Finset.sum_eq_zero
  intro p hp
  rw [Complex.ofReal_zero, analyticSmoothingPrimePhase_zero, analyticSmoothingPrimePhase_zero,
    hρ1 p ((mem_residueRamifiedPrimes p).mp hp), h1, sub_self, zero_mul]

/-- The finite ramified correction is entire in the spectral variable. -/
theorem analyticOnNhd_residueFiniteCorrection (Φ : (ZMod q)ˣ → ℂ → ℂ)
    (ρ : Nat.Primes → ℂ → ℂ) (t : ℝ) :
    AnalyticOnNhd ℂ (residueFiniteCorrection Φ ρ t) univ := by
  intro s _
  have ha : AnalyticAt ℂ (∑ p ∈ residueRamifiedPrimes q, fun s : ℂ =>
      (analyticSmoothingPrimePhase (ρ p) p (t : ℂ) -
        analyticSmoothingPrimePhase (residueAverage Φ) p (t : ℂ)) *
          ((p : ℕ) : ℂ) ^ (-s)) s := by
    apply Finset.analyticAt_sum
    intro p _
    have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    simp only [Complex.cpow_def_of_ne_zero hp]
    exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id.neg).cexp)
  have he : (∑ p ∈ residueRamifiedPrimes q, fun s : ℂ =>
      (analyticSmoothingPrimePhase (ρ p) p (t : ℂ) -
        analyticSmoothingPrimePhase (residueAverage Φ) p (t : ℂ)) *
          ((p : ℕ) : ℂ) ^ (-s)) = residueFiniteCorrection Φ ρ t := by
    funext w
    simp only [residueFiniteCorrection, Finset.sum_apply]
  rw [he] at ha
  exact ha

/-- The ramified correction is jointly continuous for nonnegative parameters. -/
theorem continuousOn_residueFiniteCorrection {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R)) :
    ContinuousOn (fun v : ℝ × ℂ => residueFiniteCorrection Φ ρ v.1 v.2)
      (Ici 0 ×ˢ univ) := by
  unfold residueFiniteCorrection
  apply continuousOn_finsetSum
  intro p hp v hv
  have ht : 0 ≤ (v.1 : ℂ).re := by simpa only [Complex.ofReal_re] using hv.1
  have hρa := (analyticAt_analyticSmoothingPrimePhase hR
    (hρ p ((mem_residueRamifiedPrimes p).mp hp)) p ht).continuousAt
  have hma := (analyticAt_analyticSmoothingPrimePhase hR
    (analyticOnNhd_residueAverage hΦ) p ht).continuousAt
  have hcast : ContinuousAt (fun v : ℝ × ℂ => (v.1 : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp continuousAt_fst
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpow : ContinuousAt (fun v : ℝ × ℂ => ((p : ℕ) : ℂ) ^ (-v.2)) v := by
    simpa only [Complex.cpow_def_of_ne_zero hp0, Pi.neg_apply] using
      ((continuousAt_snd.neg).const_mul (Complex.log ((p : ℕ) : ℂ))).cexp
  exact (((hρa.comp hcast).sub (hma.comp hcast)).mul hpow).continuousWithinAt

/-- Character inversion at each prime includes the ramified mean replacement. -/
theorem residuePrimeProfile_decomposition (Φ : (ZMod q)ˣ → ℂ → ℂ)
    (ρ : Nat.Primes → ℂ → ℂ) (p : Nat.Primes) (z : ℂ) :
    residuePrimeProfile Φ ρ p z - 1 = residueAverage Φ z - 1 +
      (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
        χ p * (residueFourierProfile Φ χ z - 1)) +
      (if (p : ℕ) ∣ q then ρ p z - residueAverage Φ z else 0) := by
  classical
  by_cases hp : IsUnit ((p : ℕ) : ZMod q)
  · have hnd : ¬ (p : ℕ) ∣ q := fun hd => (residuePrime_not_isUnit p).mpr hd hp
    have hf := residueFourier_inversion Φ hp.unit z
    simp only [hp.unit_spec] at hf
    have hs := Finset.sum_erase_add Finset.univ
      (fun χ : DirichletCharacter ℂ q => residueFourierDeviation Φ χ z * χ p)
      (Finset.mem_univ (1 : DirichletCharacter ℂ q))
    rw [hf, residueFourierDeviation_one, MulChar.one_apply hp, mul_one] at hs
    rw [residuePrimeProfile, dif_pos hp, if_neg hnd, add_zero]
    have he : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ p * (residueFourierProfile Φ χ z - 1)) =
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          residueFourierDeviation Φ χ z * χ p := by
      apply Finset.sum_congr rfl
      intro χ _
      dsimp only [residueFourierProfile]
      ring
    rw [he]
    exact hs.symm.trans (add_comm _ _)
  · have hd := (residuePrime_not_isUnit p).mp hp
    rw [residuePrimeProfile, dif_neg hp, if_pos hd]
    have hz : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ p * (residueFourierProfile Φ χ z - 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro χ _
      rw [MulChar.map_nonunit χ hp, zero_mul]
    rw [hz]
    ring

/-- The actual prime deviation is its principal mean plus nonprincipal and
finite ramified contributions. -/
theorem residuePrimeSum_decomposition {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    deformationPrimeSum (residueProfileGauge Φ ρ t) s =
      weightedProfilePrimeSum (fun _ => 1) (residueAverage Φ) t s +
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        weightedProfilePrimeSum (fun p => χ p) (residueFourierProfile Φ χ) t s) +
      residueFiniteCorrection Φ ρ t s := by
  classical
  have hm := (summable_weightedProfilePrimeTerm (a := fun _ => 1) hR (analyticOnNhd_residueAverage hΦ)
    (fun _ => by simp only [norm_one, le_refl]) ht hs).hasSum
  have hc (χ : DirichletCharacter ℂ q) := (summable_weightedProfilePrimeTerm (a := fun p => χ p) hR
    (analyticOnNhd_residueFourierProfile hΦ χ)
    (fun p => by simpa using norm_char_prime_cpow_le χ (w := 0) p) ht hs).hasSum
  have hn := hasSum_sum (s := Finset.univ.erase (1 : DirichletCharacter ℂ q))
    (fun χ _ => hc χ)
  let f : Nat.Primes → ℂ := fun p => if (p : ℕ) ∣ q then
    (analyticSmoothingPrimePhase (ρ p) p (t : ℂ) -
      analyticSmoothingPrimePhase (residueAverage Φ) p (t : ℂ)) * ((p : ℕ) : ℂ) ^ (-s)
    else 0
  have hj : HasSum f (residueFiniteCorrection Φ ρ t s) := by
    have hh := hasSum_sum_of_ne_finset_zero (s := residueRamifiedPrimes q)
      (f := f) (fun p hp => by
        dsimp only [f]
        rw [if_neg (fun hd => hp ((mem_residueRamifiedPrimes p).mpr hd))])
    convert hh using 1
    apply Finset.sum_congr rfl
    intro p hp
    exact (if_pos ((mem_residueRamifiedPrimes p).mp hp)).symm
  have hsum := (hm.add hn).add hj
  have heq (p : Nat.Primes) :
      1 * (analyticSmoothingPrimePhase (residueAverage Φ) p (t : ℂ) - 1) *
          ((p : ℕ) : ℂ) ^ (-s) +
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          χ p * (analyticSmoothingPrimePhase (residueFourierProfile Φ χ) p (t : ℂ) - 1) *
            ((p : ℕ) : ℂ) ^ (-s)) + f p =
      (twist (residueProfileGauge Φ ρ t) p - 1) * ((p : ℕ) : ℂ) ^ (-s) := by
    rw [← residuePrimeValue_eq_twist hu hρu ht p, residuePrimeValue_prime, one_mul]
    have hh := congrArg (fun z : ℂ => z * ((p : ℕ) : ℂ) ^ (-s))
      (residuePrimeProfile_decomposition Φ ρ p
        (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))))
    simp only [add_mul, Finset.sum_mul] at hh
    change _ = (residuePrimeProfile Φ ρ p
      (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) - 1) * ((p : ℕ) : ℂ) ^ (-s)
    rw [hh]
    simp only [analyticSmoothingPrimePhase, f, ite_mul, zero_mul]
  change (∑' p : Nat.Primes, (twist (residueProfileGauge Φ ρ t) p - 1) *
    ((p : ℕ) : ℂ) ^ (-s)) = _
  rw [← hsum.tsum_eq]
  exact tsum_congr (fun p => (heq p).symm)

/-- All arithmetic information outside the principal mean extends through one
and vanishes at the common endpoint. No continuation is assumed. -/
theorem exists_residuePrime_correction {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ρ p 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1) :
    ∃ e : ℝ, 0 < e ∧ ∃ K : ℝ → ℂ → ℂ,
      (∀ t : ℝ, 0 ≤ t → AnalyticOnNhd ℂ (K t) {s | 1 - e < s.re ∧ |s.im| < e}) ∧
      ContinuousOn (fun v : ℝ × ℂ => K v.1 v.2)
        (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) ∧
      (∀ s : ℂ, K 0 s = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ s : ℂ, 1 < s.re →
        deformationPrimeSum (residueProfileGauge Φ ρ t) s =
          weightedProfilePrimeSum (fun _ => 1) (residueAverage Φ) t s + K t s) := by
  classical
  obtain ⟨e, he, N, hNa, hNc, hN0, hNe⟩ :=
    exists_finite_characterProfile_continuation (residueFourierProfile Φ) hR
      (analyticOnNhd_residueFourierProfile hΦ)
      (fun _ hχ => residueFourierProfile_endpoint h1 hχ)
      (Finset.univ.erase 1) (fun _ hχ => (Finset.mem_erase.mp hχ).1)
  refine ⟨e, he, fun t s => N t s + residueFiniteCorrection Φ ρ t s,
    fun t ht => (hNa t ht).add ((analyticOnNhd_residueFiniteCorrection Φ ρ t).mono
      (subset_univ _)),
    hNc.add ((continuousOn_residueFiniteCorrection hR hΦ hρ).mono
      (fun v hv => ⟨hv.1, mem_univ _⟩)), ?_, ?_⟩
  · intro s
    rw [hN0 s, residueFiniteCorrection_zero (residueAverage_one h1) hρ1 s, add_zero]
  · intro t ht s hs
    rw [residuePrimeSum_decomposition hR hΦ hu hρu ht hs, hNe t ht s hs, add_assoc]

#print axioms residuePrimeSum_decomposition
#print axioms exists_residuePrime_correction

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
