import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Selection.Bound
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction.Readout

/-! # The three fixed-temperature regimes of an unlabelled equality measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Selection

open Filter Finset Real
open scoped Topology

def scaled (k : ℕ) (a : ℝ) (N : ℕ) :=
  (log (log N))^(k+2)*coincidence (k+2) a N

private theorem coincidence_bound (k : ℕ) (a : ℝ) (N : ℕ) {u : ℝ}
    (hu : ∀ p : PrimeAt N, Ordinary.primeProbability a N p≤u) :
    coincidence (k+2) a N ≤ u^(k+1) := by
  let q := Ordinary.primeProbability a N
  calc
    _ = ∑ p, q p^(k+1)*q p := sum_congr rfl fun p _ => pow_succ (q p) (k+1)
    _ ≤ ∑ p, u^(k+1)*q p := sum_le_sum fun p _ => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Ordinary.primeProbability_nonneg a N p) (hu p) _) (Ordinary.primeProbability_nonneg a N p)
    _ = _ := by rw [←mul_sum,Ordinary.primeProbability_sum,mul_one]

/-- Large-prime preparations dilute the equality probability faster than
its critical scale, for every nontrivial fixed number of copies. -/
theorem below_line (k : ℕ) {a : ℝ} (ha : 0<a) : Tendsto (scaled k a) atTop (𝓝 0) := by
  obtain ⟨u,un,lim,bound⟩ := atom_bound ha
  have upper := lim.pow (k+1)
  rw [zero_pow (Nat.succ_ne_zero k)] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · filter_upwards [Crossover.logEnergy_growth.eventually_ge_atTop 1] with N hN
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hN) _) (sum_nonneg fun p _ =>
      pow_nonneg (Ordinary.primeProbability_nonneg a N p) _)
  · filter_upwards [bound,Crossover.logEnergy_growth.eventually_ge_atTop 1] with N hu hL
    let L := log (log (N:ℝ))
    have h1 : 1≤L := hL
    change L^(k+2)*coincidence (k+2) a N ≤ (L^2*u N)^(k+1)
    rw [mul_pow,←pow_mul]
    exact mul_le_mul (pow_le_pow_right₀ h1 (by omega : k+2≤2*(k+1))) (coincidence_bound k a N hu)
      (sum_nonneg fun p _ => pow_nonneg (Ordinary.primeProbability_nonneg a N p) _)
      (pow_nonneg (zero_le_one.trans h1) _)

/-- On the summable side the unscaled coincidence retains positive mass. -/
theorem above_line (k : ℕ) {a : ℝ} (ha : a<0) : Tendsto (scaled k a) atTop atTop := by
  let r := k+2
  have h1 : (1:ℝ)≤(r:ℝ) := by exact_mod_cast (show 1≤r by dsimp [r]; omega)
  have shr : replicaIndex r a<0 := by
    unfold replicaIndex
    have cmp := mul_le_mul_of_nonpos_right h1 (show a-1≤0 by linarith only [ha])
    linarith only [cmp,ha]
  have pos := div_pos (primeTotal_pos shr) (pow_pos (primeTotal_pos ha) r)
  have lim := ((powerMass_limit shr).comp tendsto_natCast_atTop_atTop).div
    (((powerMass_limit ha).comp tendsto_natCast_atTop_atTop).pow r) (pow_ne_zero r (primeTotal_pos ha).ne')
  have growth : Tendsto (fun N : ℕ => (log (log N))^r) atTop atTop :=
    (tendsto_pow_atTop (by dsimp [r]; omega : r≠0)).comp Crossover.logEnergy_growth
  apply (Tendsto.atTop_mul_pos pos growth lim).congr
  intro N
  exact congrArg (fun v : ℝ => (log (log N))^r*v) (coincidence_eq (a:=a) (N:=N) (by dsimp [r]; omega : 0<r)).symm

theorem on_line (k : ℕ) : Tendsto (scaled k 0) atTop (𝓝 (_root_.RHTower.primeZeta ((k+2:ℕ):ℝ))) :=
  Reconstruction.reading_limit k

/-- Any one fixed replica count selects the full composition isometry by a
finite positive scaled probability, using no prime label or clock calibration. -/
theorem isometric_iff (k : ℕ) (s : ℂ) :
    (∃ v : ℝ, 0<v ∧ Tendsto (fun N => Reconstruction.waveReading k s N) atTop (𝓝 v)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [split_isometric_iff]
  have readout : (fun N => Reconstruction.waveReading k s N)=scaled k (1-2*s.re) :=
    funext fun N => Reconstruction.wave_reading k s N
  rw [readout]
  constructor
  · rintro ⟨v,hv,lim⟩
    rcases lt_trichotomy (1-2*s.re) 0 with h|h|h
    · have gt := (above_line k h).eventually_gt_atTop (v+1)
      have lt := lim.eventually_lt_const (lt_add_one v)
      obtain ⟨_,p,q⟩ := (gt.and lt).exists
      exact False.elim (p.asymm q)
    · linarith only [h]
    · exact False.elim (hv.ne' (tendsto_nhds_unique lim (below_line k h)))
  · intro h
    rw [show 1-2*s.re=0 by rw [h]; ring]
    refine ⟨_,?_,on_line k⟩
    rw [←total_eq_primeZeta]
    exact primeTotal_pos (replicated_negative k)

#print axioms below_line
#print axioms above_line
#print axioms isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Selection
