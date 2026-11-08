import GaloisForLFunctions.SurfaceOfSpecZ.ThePlaneCountsAtTheIntegerDegrees
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Hasse–Weil for pairs of prime degrees is RH

`SparseDegreesDecideRH` asks whether the prime degrees alone decide RH through the planes
`⟨Γ_1, Γ_p⟩`; that needs prime gaps `O(√p)`. Through the planes `⟨Γ_p, Γ_q⟩` spanned by two smoothed
Frobenius graphs of prime degree no gap condition is needed: their defect is `c_B(log p − log q)`
(`defect_frobeniusPair`), and the log-ratios of primes are dense (`dense_primeLogRatios`) because
for every `ε > 0` every large `x` has a prime in `(x, (1 + ε)x)` (the prime number theorem,
`PNTPlus.prime_between`). By continuity of the orbit correlation the test on prime pairs is the test at
every real scale (`riemannHypothesis_iff_forall_primePair_hasseWeil`).

So the Frobenius graphs of prime degree decide RH by their mutual Castelnuovo–Severi inequalities, as
the graphs of `F` and its powers do on `C × C`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri

/-- The log-ratios of primes are dense in `ℝ`. -/
theorem dense_primeLogRatios :
    Dense {t : ℝ | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ t = Real.log p - Real.log q} := by
  rw [Metric.dense_iff]
  intro v ε hε
  -- a prime `p` just above `q eᵛ` for a large prime `q`
  set δ := Real.exp ε - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ, sub_pos]; exact Real.one_lt_exp_iff.mpr hε
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (prime_between hδ0)
  obtain ⟨q, hqX, hq⟩ := Nat.exists_infinite_primes ⌈X / Real.exp v⌉₊
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hxX : X ≤ q * Real.exp v := by
    have h1 : X / Real.exp v ≤ q := (Nat.ceil_le.mp hqX)
    rw [div_le_iff₀ (Real.exp_pos v)] at h1; linarith
  obtain ⟨p, hp, hpx, hpx'⟩ := hX _ hxX
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨Real.log p - Real.log q, ?_, ⟨p, q, hp, hq, rfl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, ← Real.log_div hp0.ne' hq0.ne']
  have hlo : Real.exp v < p / q := by rw [lt_div_iff₀ hq0]; linarith
  have hhi : p / q < Real.exp (v + ε) := by
    rw [div_lt_iff₀ hq0, Real.exp_add]
    calc (p : ℝ) < (1 + δ) * (q * Real.exp v) := hpx'
      _ = Real.exp v * Real.exp ε * q := by rw [hδ]; ring
  have h1 : v < Real.log (p / q) := (Real.lt_log_iff_exp_lt (div_pos hp0 hq0)).mpr hlo
  have h2 : Real.log (p / q) < v + ε := (Real.log_lt_iff_lt_exp (div_pos hp0 hq0)).mpr hhi
  rw [abs_lt]; constructor <;> linarith

/-- **Hasse–Weil for every pair of smoothed Frobenius graphs of prime degree is RH.** -/
theorem riemannHypothesis_iff_forall_primePair_hasseWeil :
    RiemannHypothesis ↔ ∀ p q : ℕ, p.Prime → q.Prime →
      zetaScalingDatum.HasseWeilAt splineCycle (Real.log p - Real.log q) := by
  rw [riemannHypothesis_iff_splineOrbit_hasseWeil]
  constructor
  · intro h p q _ _; exact h _
  · intro h
    have hcont := continuous_zetaOrbitCorr' splineCycle
    have hclosed : IsClosed {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by
      simp only [ScalingDatum.HasseWeilAt]
      exact isClosed_le (continuous_abs.comp hcont) continuous_const
    have hsub : {t : ℝ | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ t = Real.log p - Real.log q} ⊆
        {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by
      rintro _ ⟨p, q, hp, hq, rfl⟩
      exact h p q hp hq
    have huniv := (dense_primeLogRatios.mono hsub).closure_eq
    rw [hclosed.closure_eq] at huniv
    intro t
    have : t ∈ {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by rw [huniv]; trivial
    exact this

end GaloisForLFunctions.SurfaceOfSpecZ
