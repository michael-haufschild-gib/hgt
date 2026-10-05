import GaloisForLFunctions.RHTower.ChiRamanujanPrimeOnlyAtoms
import GaloisForLFunctions.RHTower.ChiRamanujanThreeFrequencyAtomAction

/-!
# Joint prime-only three-frequency rational source

The complete finite atom tensor converges against every fixed Schwartz
Fourier profile to the product of the three prime logarithms. The squarefree
projector belongs to the source, so the original smooth test is retained.
All rational atoms and all independent integer frequencies remain. This
fixed-test theorem supplies no estimate for the growing physical cubic.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology SchwartzMap
namespace RHTower.BAGTrace

def ramanujanTriplePrimeOnlyCoeff (P : Finset ℕ) (ε : ℝ) (n : ℤ × ℤ × ℤ) : ℝ :=
  ramanujanPrimeOnlyMultiplier P ε n.1.natAbs *
    ramanujanPrimeOnlyMultiplier P ε n.2.1.natAbs *
      ramanujanPrimeOnlyMultiplier P ε n.2.2.natAbs

def ramanujanTriplePrimeLogCoeff (n : ℤ × ℤ × ℤ) : ℝ :=
  (if n.1.natAbs.Prime then Real.log n.1.natAbs else 0) *
    (if n.2.1.natAbs.Prime then Real.log n.2.1.natAbs else 0) *
      (if n.2.2.natAbs.Prime then Real.log n.2.2.natAbs else 0)

def ramanujanTriplePrimeOnlyTest (P : Finset ℕ) (ε : ℝ)
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) : ℂ :=
  ∑' n : ℤ × ℤ × ℤ, Φ (ramanujanTripleLattice n) * (ramanujanTriplePrimeOnlyCoeff P ε n : ℂ)

def ramanujanTriplePrimeLogTest (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) : ℂ :=
  ∑' n : ℤ × ℤ × ℤ, Φ (ramanujanTripleLattice n) * (ramanujanTriplePrimeLogCoeff n : ℂ)

theorem ramanujanTriplePrimeOnlyCoeff_bounds {P : Finset ℕ}
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℤ × ℤ × ℤ) :
    0 ≤ ramanujanTriplePrimeOnlyCoeff P ε n ∧
      ramanujanTriplePrimeOnlyCoeff P ε n ≤
        6^3 * ramanujanTripleWeight (ramanujanTripleLattice n) := by
  have h1 := ramanujanSquareSieveWeight_bounds P n.1.natAbs
  have h2' := ramanujanSquareSieveWeight_bounds P n.2.1.natAbs
  have h3' := ramanujanSquareSieveWeight_bounds P n.2.2.natAbs
  let A := ramanujanSquareSieveWeight P n.1.natAbs *
    ramanujanSquareSieveWeight P n.2.1.natAbs * ramanujanSquareSieveWeight P n.2.2.natAbs
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg h1.1 h2'.1) h3'.1
  have hA1 : A ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul (mul_le_mul h1.2 h2'.2 h2'.1 (by norm_num)) h3'.2 h3'.1 (by norm_num)
  have he : ramanujanTriplePrimeOnlyCoeff P ε n = A * ramanujanTripleCompensatedCoeff P ε n := by
    dsimp [ramanujanTriplePrimeOnlyCoeff, ramanujanPrimeOnlyMultiplier,
      ramanujanTripleCompensatedCoeff, A]
    ring
  rw [he]
  obtain ⟨hc0,hc1⟩ := ramanujanTripleCompensatedCoeff_bounds h2 h3 hε hε1 n
  exact ⟨mul_nonneg hA0 hc0,
    (mul_le_mul_of_nonneg_right hA1 hc0).trans (by simpa only [one_mul] using hc1)⟩

theorem tendsto_ramanujanTriplePrimeOnlyCoeff (n : ℤ × ℤ × ℤ) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanTriplePrimeOnlyCoeff z.1 z.2 n)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (ramanujanTriplePrimeLogCoeff n)) :=
  ((tendsto_ramanujanPrimeOnlyMultiplier n.1.natAbs).mul
    (tendsto_ramanujanPrimeOnlyMultiplier n.2.1.natAbs)).mul
      (tendsto_ramanujanPrimeOnlyMultiplier n.2.2.natAbs)

/-- The source removes proper prime powers before testing, with no cutoff/damping coupling. -/
theorem tendsto_ramanujanTriplePrimeOnlyTest (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanTriplePrimeOnlyTest z.1 z.2 Φ)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (ramanujanTriplePrimeLogTest Φ)) := by
  apply tendsto_tsum_of_dominated_convergence
    ((summable_ramanujanTripleSchwartz_weighted Φ).mul_left (6^3))
  · intro n
    exact (Complex.continuous_ofReal.tendsto _ |>.comp
      (tendsto_ramanujanTriplePrimeOnlyCoeff n)).const_mul _
  · have hP : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ({2,3} : Finset ℕ) ⊆ z.1 :=
      tendsto_fst.eventually (eventually_ge_atTop {2,3})
    have hp : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), 0 < z.2 :=
      tendsto_snd.eventually self_mem_nhdsWithin
    have h1 : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), z.2 ≤ 1 :=
      tendsto_snd.eventually
        ((eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
    filter_upwards [hP,hp,h1] with z hz hp h1 n
    obtain ⟨hn0,hn⟩ := ramanujanTriplePrimeOnlyCoeff_bounds
      (hz (by simp)) (hz (by simp)) hp h1 n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn0]
    exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (by ring)

abbrev RamanujanTriplePrimeOnlyAtomIndex (P : Finset ℕ) :=
  RamanujanPrimeOnlyAtomIndex P × RamanujanPrimeOnlyAtomIndex P × RamanujanPrimeOnlyAtomIndex P

def ramanujanTriplePrimeOnlyAtomNode {P : Finset ℕ}
    (a : RamanujanTriplePrimeOnlyAtomIndex P) : ℝ × ℝ × ℝ :=
  (ramanujanPrimeOnlyAtomNode a.1, ramanujanPrimeOnlyAtomNode a.2.1, ramanujanPrimeOnlyAtomNode a.2.2)

def ramanujanTriplePrimeOnlyAtomWeight (P : Finset ℕ) (ε : ℝ)
    (a : RamanujanTriplePrimeOnlyAtomIndex P) : ℝ :=
  ramanujanPrimeOnlyAtomWeight P ε a.1 * ramanujanPrimeOnlyAtomWeight P ε a.2.1 *
    ramanujanPrimeOnlyAtomWeight P ε a.2.2

def ramanujanTriplePrimeOnlyAtomAction (P : Finset ℕ) (ε : ℝ)
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) : ℂ :=
  ∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
    (ramanujanTriplePrimeOnlyAtomWeight P ε a : ℂ) *
      ramanujanTriplePeriodicTest Φ (ramanujanTriplePrimeOnlyAtomNode a)

theorem sum_ramanujanTriplePrimeOnlyAtomWeight_fourier (P : Finset ℕ) (ε : ℝ)
    (n : ℤ × ℤ × ℤ) :
    (∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
      (ramanujanTriplePrimeOnlyAtomWeight P ε a : ℂ) *
        ramanujanTripleFourierPhase n (ramanujanTriplePrimeOnlyAtomNode a)) =
      (ramanujanTriplePrimeOnlyCoeff P ε n : ℂ) := by
  classical
  rw [ramanujanTriplePrimeOnlyCoeff, Complex.ofReal_mul, Complex.ofReal_mul,
    ← sum_ramanujanPrimeOnlyAtomWeight_fourier P ε n.1,
    ← sum_ramanujanPrimeOnlyAtomWeight_fourier P ε n.2.1,
    ← sum_ramanujanPrimeOnlyAtomWeight_fourier P ε n.2.2]
  conv_rhs => rw [mul_assoc]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  dsimp [ramanujanTriplePrimeOnlyAtomWeight, ramanujanTripleFourierPhase,
    ramanujanTriplePrimeOnlyAtomNode]
  push_cast
  ring

/-- Full rational atom/Fourier interchange retains the original smooth profile. -/
theorem ramanujanTriplePrimeOnlyAtomAction_eq (P : Finset ℕ) (ε : ℝ)
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    ramanujanTriplePrimeOnlyAtomAction P ε Φ = ramanujanTriplePrimeOnlyTest P ε Φ := by
  classical
  have hs (a : RamanujanTriplePrimeOnlyAtomIndex P) : Summable (fun n : ℤ × ℤ × ℤ =>
      (ramanujanTriplePrimeOnlyAtomWeight P ε a : ℂ) *
        (Φ (ramanujanTripleLattice n) *
          ramanujanTripleFourierPhase n (ramanujanTriplePrimeOnlyAtomNode a))) :=
    (summable_ramanujanTriplePeriodicTest Φ (ramanujanTriplePrimeOnlyAtomNode a)).mul_left _
  unfold ramanujanTriplePrimeOnlyAtomAction ramanujanTriplePeriodicTest
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun a _ => hs a)]
  apply tsum_congr
  intro n
  calc
    _ = Φ (ramanujanTripleLattice n) *
        ∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
          (ramanujanTriplePrimeOnlyAtomWeight P ε a : ℂ) *
            ramanujanTripleFourierPhase n (ramanujanTriplePrimeOnlyAtomNode a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by rw [sum_ramanujanTriplePrimeOnlyAtomWeight_fourier]

/-- Joint critical limit of all finite rational atoms, with exact prime-only coefficients. -/
theorem tendsto_ramanujanTriplePrimeOnlyAtomAction (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanTriplePrimeOnlyAtomAction z.1 z.2 Φ)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (ramanujanTriplePrimeLogTest Φ)) := by
  simpa only [ramanujanTriplePrimeOnlyAtomAction_eq] using tendsto_ramanujanTriplePrimeOnlyTest Φ

end RHTower.BAGTrace
