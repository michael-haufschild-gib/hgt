import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Readout
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Posterior
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Selection.Bound

/-! # A single vacuum detector selects the isometric composition line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum

open Filter Finset Real
open scoped Topology
open Collisions

private theorem survival (a x : ℝ) (j : ℕ) :
    powerMass (a-(j:ℝ)) x/powerMass a x =
      ∑ p : PrimeAt x, Ordinary.primeProbability a x p*(p.val:ℝ)^(-(j:ℝ)) := by
  have term (p : PrimeAt x) : Ordinary.primeProbability a x p*(p.val:ℝ)^(-(j:ℝ))=
      (p.val:ℝ)^(a-(j:ℝ)-1)/powerMass a x := by
    have pos := (Nat.cast_pos.mpr (Nat.mem_primesBelow.mp p.property).2.pos : 0<(p.val:ℝ))
    have h : exp ((a-1)*energy (primeLabel p))=(p.val:ℝ)^(a-1) := by
      rw [rpow_def_of_pos pos,mul_comm]
      rfl
    rw [Ordinary.primeProbability,h,div_mul_eq_mul_div,←rpow_add pos]
    rw [show a-1 + -(j:ℝ)=a-(j:ℝ)-1 by ring]
  simp only [term,←sum_div]
  exact congrArg (fun v : ℝ => v/powerMass a x)
    (sum_coe_sort (primes (cutoff x)) (fun p : ℕ => (p:ℝ)^(a-(j:ℝ)-1))).symm

private theorem upper {a x u : ℝ} (k : ℕ) (hu : 0≤u)
    (bound : ∀ p : PrimeAt x, Ordinary.primeProbability a x p≤u) :
    powerMass (a-((k+1:ℕ):ℝ)) x/powerMass a x≤u*powerMass 0 x := by
  rw [survival]
  calc
    _ ≤ ∑ p : PrimeAt x, u*(p.val:ℝ)^((0:ℝ)-1) := by
      refine sum_le_sum fun p _ => mul_le_mul (bound p) ?_ (rpow_nonneg (Nat.cast_nonneg _) _) hu
      apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.mem_primesBelow.mp p.property).2.one_lt.le)
      push_cast
      linarith only [(Nat.cast_nonneg k : 0≤(k:ℝ))]
    _ = _ := by
      rw [←mul_sum]
      exact congrArg (fun v : ℝ => u*v)
        (sum_coe_sort (primes (cutoff x)) (fun p : ℕ => (p:ℝ)^((0:ℝ)-1)))

def scaled (k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) (N : ℕ) :=
  log (log N)*probability 1 s N (z N) (k+1)

theorem diluted (k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) (ha : 0<1-2*s.re) :
    Tendsto (scaled k s z) atTop (𝓝 0) := by
  obtain ⟨u,un,lim,bound⟩ := Selection.atom_bound ha
  have h := lim.mul (harmonic_mass_ratio.comp tendsto_natCast_atTop_atTop)
  rw [zero_mul] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards [Crossover.logEnergy_growth.eventually_gt_atTop 0] with N hL
    exact mul_nonneg hL.le (sq_nonneg _)
  · filter_upwards [Crossover.logEnergy_growth.eventually_gt_atTop 0,bound] with N hL hN
    let L := log (log (N:ℝ))
    have pos : 0<L := hL
    change L*probability 1 s N (z N) (k+1) ≤ (L^2*u N)*(powerMass 0 N/L)
    rw [probability_eq,pow_one]
    calc
      _ ≤ L*(u N*powerMass 0 N) := mul_le_mul_of_nonneg_left (upper k (un N) hN) pos.le
      _ = _ := by field_simp [pos.ne']

theorem persistent (k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) (ha : 1-2*s.re<0) :
    Tendsto (scaled k s z) atTop atTop := by
  let a := 1-2*s.re
  have neg : a-((k+1:ℕ):ℝ)<0 := sub_neg.mpr
    ((show a<0 from ha).trans_le (Nat.cast_nonneg _))
  have ratio := ((powerMass_limit neg).comp tendsto_natCast_atTop_atTop).div
    ((powerMass_limit ha).comp tendsto_natCast_atTop_atTop) (primeTotal_pos ha).ne'
  have h := Tendsto.atTop_mul_pos (div_pos (primeTotal_pos neg) (primeTotal_pos ha))
    Crossover.logEnergy_growth ratio
  apply h.congr
  intro N
  change log (log N)*(powerMass (a-((k+1:ℕ):ℝ)) N/powerMass a N)=_
  rw [scaled,probability_eq,pow_one]

/-- A fixed depth and a single elementary excitation suffice. At any
other input temperature the scaled probability vanishes or diverges. -/
theorem isometric_iff (k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) :
    (∃ v : ℝ, 0<v ∧ Tendsto (scaled k s z) atTop (𝓝 v)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [split_isometric_iff]
  constructor
  · rintro ⟨v,hv,h⟩
    rcases lt_trichotomy (1-2*s.re) 0 with ha|ha|ha
    · obtain ⟨_,p,q⟩ := (((persistent k s z ha).eventually_gt_atTop (v+1)).and
        (h.eventually_lt_const (lt_add_one v))).exists
      exact False.elim (p.asymm q)
    · linarith only [ha]
    · exact False.elim (hv.ne' (tendsto_nhds_unique h (diluted k s z ha)))
  · intro hs
    refine ⟨_,?_,reading_limit (fun _ => ⟨s,hs⟩) z k⟩
    rw [←total_eq_primeZeta]
    exact primeTotal_pos (replicated_negative k)

private theorem sector_scaled (m k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) (N : ℕ) :
    (log (log N))^m*probability m s N (z N) (k+1)=(scaled k s z N)^m := by
  rw [scaled,mul_pow,probability_eq,probability_eq,pow_one]

/-- Exactly the vacuum sector accepts all input temperatures. Every positive
occupation sector selects the same full-space isometry at each positive depth. -/
theorem sector_isometric_iff (m k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) :
    (∃ v : ℝ, 0<v ∧ Tendsto (fun N : ℕ => (log (log N))^m*probability m s N (z N) (k+1))
      atTop (𝓝 v)) ↔ m=0 ∨ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  simp only [sector_scaled]
  cases m with
  | zero =>
    simp only [pow_zero]
    exact iff_of_true ⟨1,zero_lt_one,tendsto_const_nhds⟩ (Or.inl True.intro)
  | succ m =>
    rw [or_iff_right (Nat.succ_ne_zero m),split_isometric_iff]
    constructor
    · rintro ⟨v,hv,h⟩
      rcases lt_trichotomy (1-2*s.re) 0 with ha|ha|ha
      · have grow := (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp (persistent k s z ha)
        obtain ⟨_,p,q⟩ := ((grow.eventually_gt_atTop (v+1)).and (h.eventually_lt_const (lt_add_one v))).exists
        exact False.elim (p.asymm q)
      · linarith only [ha]
      · have vanish := (diluted k s z ha).pow (m+1)
        rw [zero_pow (Nat.succ_ne_zero m)] at vanish
        exact False.elim (hv.ne' (tendsto_nhds_unique h vanish))
    · intro hs
      obtain ⟨v,hv,h⟩ := (isometric_iff k s z).mpr ((split_isometric_iff s).mpr hs)
      exact ⟨v^(m+1),pow_pos hv _,h.pow _⟩

#print axioms diluted
#print axioms persistent
#print axioms isometric_iff
#print axioms sector_isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum
