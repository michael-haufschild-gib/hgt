import GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockGammaBand
import GaloisForLFunctions.RHTower.EulerHellingerLocalGrowthBounds
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Resonance of the entire initial-prime critical Euler product

On the existing positive-width resonance band, primes above the square-root
horizon do not contract. Primes below it have a total squared-modulus loss
bounded by `exp(-16 sqrt(sqrt y))`. This is smaller than the exponential gain
from the terminal window. The theorem retains every prime up to the endpoint;
no freely chosen coefficient array or omitted-prime premise is used.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private lemma prime_radius_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ mobiusCriticalPrimeRadius p ∧ mobiusCriticalPrimeRadius p ≤ 3/4 := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hs : (Real.sqrt p)^2 = p := Real.sq_sqrt (by positivity)
  constructor
  · exact inv_nonneg.mpr hs0.le
  · change (Real.sqrt p)⁻¹ ≤ 3/4
    rw [← one_div]
    apply (div_le_iff₀ hs0).mpr
    nlinarith [sq_nonneg (Real.sqrt p-4/3)]

private lemma factor_loss {p : ℕ} (hp : p.Prime) (t : ℝ) :
    Real.exp (-8/Real.sqrt p) ≤ ‖mobiusCriticalPrimeFactor p t‖^2 := by
  obtain ⟨hr0,hr⟩ := prime_radius_bounds hp
  have hlog := neg_log_one_sub_le_of_le hr0 hr (by norm_num : (3/4:ℝ)<1)
  norm_num at hlog
  have hpos : 0 < 1-mobiusCriticalPrimeRadius p := by linarith
  have he : Real.exp (-4*mobiusCriticalPrimeRadius p) ≤ 1-mobiusCriticalPrimeRadius p := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs := mul_self_le_mul_self (Real.exp_pos _).le he
  have hn := normSq_mobiusCriticalPrimeFactor hp.pos t
  rw [Complex.normSq_eq_norm_sq] at hn
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (t*Real.log p))
    (by positivity : 0 ≤ 2*mobiusCriticalPrimeRadius p)
  have hsq : (1-mobiusCriticalPrimeRadius p)^2 ≤ ‖mobiusCriticalPrimeFactor p t‖^2 := by
    nlinarith only [hn,hcos]
  have heq : Real.exp (-8/Real.sqrt p) =
      Real.exp (-4*mobiusCriticalPrimeRadius p)*Real.exp (-4*mobiusCriticalPrimeRadius p) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [mobiusCriticalPrimeRadius]
    ring
  rw [heq]
  exact hs.trans (by simpa only [pow_two] using hsq)

private lemma high_prime_phase {y t : ℝ} (hy : 1 < y)
    (ht : t ∈ Icc (Real.pi/Real.log y) (4*Real.pi/(3*Real.log y)))
    {p : ℕ} (hp : p.Prime) (hlo : Real.sqrt y ≤ p) (hhi : (p:ℝ) ≤ y) :
    Real.cos (t*Real.log p) ≤ 0 := by
  have hy0 : 0<y := by linarith
  have hl : 0<Real.log y := Real.log_pos hy
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpl : 0≤Real.log p := (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hlogs := Real.log_le_log (Real.sqrt_pos.mpr hy0) hlo
  rw [Real.log_sqrt hy0.le] at hlogs
  have hlogp := Real.log_le_log hp0 hhi
  have ht0 : 0≤t := (div_nonneg Real.pi_pos.le hl.le).trans ht.1
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · calc
      Real.pi/2 = (Real.pi/Real.log y)*(Real.log y/2) := by field_simp
      _ ≤ t*Real.log p := mul_le_mul ht.1 hlogs (by positivity) ht0
  · have h := mul_le_mul ht.2 hlogp hpl
        (by positivity : 0≤4*Real.pi/(3*Real.log y))
    have he : (4*Real.pi/(3*Real.log y))*Real.log y = 4*Real.pi/3 := by field_simp
    rw [he] at h
    nlinarith [Real.pi_pos]

private lemma factor_noncontracting {y t : ℝ} (hy : 1<y)
    (ht : t ∈ Icc (Real.pi/Real.log y) (4*Real.pi/(3*Real.log y)))
    {p : ℕ} (hp : p.Prime) (hlo : Real.sqrt y ≤ p) (hhi : (p:ℝ)≤y) :
    1≤‖mobiusCriticalPrimeFactor p t‖^2 := by
  have hn := normSq_mobiusCriticalPrimeFactor hp.pos t
  rw [Complex.normSq_eq_norm_sq] at hn
  have hc := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤2*mobiusCriticalPrimeRadius p by dsimp [mobiusCriticalPrimeRadius]; positivity)
    (high_prime_phase hy ht hp hlo hhi)
  nlinarith [sq_nonneg (mobiusCriticalPrimeRadius p)]

private lemma small_prime_sum_le (R : Finset ℕ) (hR : ∀ p∈R,p.Prime)
    {y : ℝ} :
    (∑p∈R, if (p:ℝ)<Real.sqrt y then 1/Real.sqrt p else 0) ≤
      2*Real.sqrt (Real.sqrt y) := by
  rw [← Finset.sum_filter]
  have hsub : R.filter (fun p : ℕ => (p:ℝ)<Real.sqrt y) ⊆ Finset.Icc 1 ⌊Real.sqrt y⌋₊ := by
    intro p hp
    obtain ⟨hpR,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(hR p hpR).one_lt.le,Nat.le_floor hp.le⟩
  calc
    _ ≤ ∑ p∈Icc 1 ⌊Real.sqrt y⌋₊,(1:ℝ)/Real.sqrt p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2*Real.sqrt (⌊Real.sqrt y⌋₊:ℝ) := sum_one_div_sqrt_le _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.floor_le (Real.sqrt_nonneg y))) (by norm_num)

/-- The entire initial-prime product retains the terminal-window gain; all possible
loss comes from primes below the square-root horizon. -/
theorem mobiusCriticalInitialPrime_norm_sq_lower_on_gammaBand {y t : ℝ} (hy : 27≤y)
    (ht : t ∈ Icc (Real.pi/Real.log y) (4*Real.pi/(3*Real.log y))) :
    Real.exp (-16*Real.sqrt (Real.sqrt y)) *
      (1+1/Real.sqrt y)^(mobiusCriticalPrimeWindow y).card ≤
      ‖∏p∈windowPrimes 0 y,mobiusCriticalPrimeFactor p t‖^2 := by
  have hy0 : 0≤y := by linarith
  let Q := windowPrimes 0 y
  let P := mobiusCriticalPrimeWindow y
  let R := Q \ P
  have hQ (p : ℕ) (hp : p∈Q) : p.Prime ∧ (p:ℝ)≤y := by
    obtain ⟨hpp,_,hpy⟩ := (mem_windowPrimes (by norm_num) hy0).mp hp
    exact ⟨hpp,hpy⟩
  have hPQ : P⊆Q := by
    intro p hp
    obtain ⟨hpp,_,hpy⟩ := (mem_windowPrimes (by positivity) hy0).mp hp
    exact (mem_windowPrimes (by norm_num) hy0).mpr
      ⟨hpp,by exact_mod_cast hpp.pos,hpy⟩
  have hR (p : ℕ) (hp : p∈R) : p.Prime ∧ (p:ℝ)≤y := hQ p (Finset.mem_sdiff.mp hp).1
  let u : ℕ → ℝ := fun p => if (p:ℝ)<Real.sqrt y then 1/Real.sqrt p else 0
  have hpoint (p : ℕ) (hp : p∈R) : Real.exp (-8*u p) ≤ ‖mobiusCriticalPrimeFactor p t‖^2 := by
    dsimp [u]
    split_ifs with hpSmall
    · simpa only [mul_one_div] using factor_loss (hR p hp).1 t
    · simpa only [mul_zero,Real.exp_zero] using
        factor_noncontracting (by linarith : 1<y) ht (hR p hp).1 (le_of_not_gt hpSmall) (hR p hp).2
  have hprod := Finset.prod_le_prod (fun p hp => (Real.exp_pos (-8*u p)).le) hpoint
  rw [← Real.exp_sum,← Finset.mul_sum] at hprod
  have hsum := small_prime_sum_le R (fun p hp => (hR p hp).1) (y := y)
  have hloss : Real.exp (-16*Real.sqrt (Real.sqrt y)) ≤
      ∏p∈R,‖mobiusCriticalPrimeFactor p t‖^2 := by
    apply le_trans _ hprod
    apply Real.exp_le_exp.mpr
    change (∑ p∈R,u p) ≤ 2*Real.sqrt (Real.sqrt y) at hsum
    linarith
  have hwindow := mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand hy ht.1 ht.2
  have hmult := mul_le_mul hloss hwindow (by positivity)
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
  have he : R∪P=Q := Finset.sdiff_union_of_subset hPQ
  have hd : Disjoint R P := Finset.sdiff_disjoint
  rw [norm_prod,← Finset.prod_pow]
  change _ ≤ ∏p∈Q,‖mobiusCriticalPrimeFactor p t‖^2
  rw [← he,Finset.prod_union hd]
  simpa only [mobiusCriticalPrimeBlock,norm_prod,← Finset.prod_pow] using hmult

end RHTower
