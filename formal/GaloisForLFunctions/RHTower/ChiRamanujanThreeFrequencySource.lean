import GaloisForLFunctions.RHTower.ChiRamanujanFinitePrimeCompensation
import GaloisForLFunctions.RHTower.ChiRamanujanThreeFrequencyLattice

/-!
# Joint three-coordinate Fourier source limit

The actual finite-prime compensated multipliers converge jointly against
every Schwartz test. All independent integer coordinates, including zero,
are retained. This is not a bound for a growing physical test.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology SchwartzMap
namespace RHTower.BAGTrace

def ramanujanTripleCompensatedCoeff (P : Finset ℕ) (ε : ℝ) (n : ℤ × ℤ × ℤ) : ℝ :=
  ramanujanCompensatedMultiplier P ε n.1.natAbs *
    ramanujanCompensatedMultiplier P ε n.2.1.natAbs *
      ramanujanCompensatedMultiplier P ε n.2.2.natAbs

def ramanujanTripleMangoldtCoeff (n : ℤ × ℤ × ℤ) : ℝ :=
  vonMangoldt n.1.natAbs * vonMangoldt n.2.1.natAbs * vonMangoldt n.2.2.natAbs

/-- All three integer Fourier coordinates remain independent. -/
def ramanujanTripleCompensatedTest (P : Finset ℕ) (ε : ℝ)
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) : ℂ :=
  ∑' n : ℤ × ℤ × ℤ, Φ (ramanujanTripleLattice n) * (ramanujanTripleCompensatedCoeff P ε n : ℂ)

def ramanujanTripleMangoldtTest (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) : ℂ :=
  ∑' n : ℤ × ℤ × ℤ, Φ (ramanujanTripleLattice n) * (ramanujanTripleMangoldtCoeff n : ℂ)

theorem ramanujanTripleCompensatedCoeff_bounds {P : Finset ℕ}
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℤ × ℤ × ℤ) :
    0 ≤ ramanujanTripleCompensatedCoeff P ε n ∧
      ramanujanTripleCompensatedCoeff P ε n ≤
        6^3 * ramanujanTripleWeight (ramanujanTripleLattice n) := by
  have h1 := ramanujanCompensatedMultiplier_nat_bound h2 h3 hε hε1 n.1.natAbs
  have h2' := ramanujanCompensatedMultiplier_nat_bound h2 h3 hε hε1 n.2.1.natAbs
  have h3' := ramanujanCompensatedMultiplier_nat_bound h2 h3 hε hε1 n.2.2.natAbs
  have habs (m : ℤ) : (m.natAbs : ℝ) = |(m : ℝ)| := by
    cases m <;> simp
    rename_i k
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) k])]
    ring
  refine ⟨mul_nonneg (mul_nonneg h1.1 h2'.1) h3'.1, ?_⟩
  calc
    _ ≤ (6 * (1 + (n.1.natAbs : ℝ))) * (6 * (1 + (n.2.1.natAbs : ℝ))) *
        (6 * (1 + (n.2.2.natAbs : ℝ))) :=
      mul_le_mul (mul_le_mul h1.2 h2'.2 h2'.1 (by positivity)) h3'.2 h3'.1 (by positivity)
    _ = _ := by simp only [habs, ramanujanTripleWeight, ramanujanTripleLattice]; ring

theorem tendsto_ramanujanTripleCompensatedCoeff (n : ℤ × ℤ × ℤ) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanTripleCompensatedCoeff z.1 z.2 n)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (ramanujanTripleMangoldtCoeff n)) :=
  ((tendsto_ramanujanCompensatedMultiplier n.1.natAbs).mul
    (tendsto_ramanujanCompensatedMultiplier n.2.1.natAbs)).mul
      (tendsto_ramanujanCompensatedMultiplier n.2.2.natAbs)

/-- The full three-frequency source has a joint critical limit against every Schwartz test.
The theorem imposes neither a resonance equation nor absolute summability of rational atoms. -/
theorem tendsto_ramanujanTripleCompensatedTest (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanTripleCompensatedTest z.1 z.2 Φ)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (ramanujanTripleMangoldtTest Φ)) := by
  apply tendsto_tsum_of_dominated_convergence
    ((summable_ramanujanTripleSchwartz_weighted Φ).mul_left (6^3))
  · intro n
    exact (Complex.continuous_ofReal.tendsto _ |>.comp
      (tendsto_ramanujanTripleCompensatedCoeff n)).const_mul _
  · have hP : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ({2,3} : Finset ℕ) ⊆ z.1 :=
      tendsto_fst.eventually (eventually_ge_atTop {2,3})
    have hp : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), 0 < z.2 :=
      tendsto_snd.eventually self_mem_nhdsWithin
    have h1 : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), z.2 ≤ 1 :=
      tendsto_snd.eventually
        ((eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
    filter_upwards [hP,hp,h1] with z hz hp h1 n
    obtain ⟨hn0, hn⟩ := ramanujanTripleCompensatedCoeff_bounds
      (hz (by simp)) (hz (by simp)) hp h1 n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn0]
    exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (by ring)

end RHTower.BAGTrace
