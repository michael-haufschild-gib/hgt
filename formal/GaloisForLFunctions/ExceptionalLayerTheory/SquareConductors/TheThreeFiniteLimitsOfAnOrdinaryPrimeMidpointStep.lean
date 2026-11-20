import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import GaloisForLFunctions.RHTower.PrimeDeletionGreedyConstruction

/-!
# Finite limits of a single ordinary-prime midpoint increment

Only five candidate primes survive the even and triple endpoints of a
one-step displacement. On a fixed primality pattern the increment equals
an integral multiple of log n plus a constant and a vanishing error.
A finite limit requires equal total incoming and outgoing multiplicities.
This leaves zero, log(9/8), and log(9/16). The two nonzero limits encode
recurring three-prime configurations.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def primeMidpointStep (n : ℕ) := primeMidpointPrice (n+1)-primeMidpointPrice n

/-- The two middle sites, the single left site, and the two right sites,
in that order. Their weights in the increment are 2, 2, −1, −1, −1. -/
def midpointStepPattern (n : ℕ) : Fin 5 → Bool :=
  ![decide (3*n+1).Prime,decide (3*n+2).Prime,decide (2*n+1).Prime,
    decide (4*n+1).Prime,decide (4*n+3).Prime]

private def stepMiddle (P : Fin 5 → Bool) := (P 0).toNat+(P 1).toNat
private def stepLeft (P : Fin 5 → Bool) := (P 2).toNat
private def stepRight (P : Fin 5 → Bool) := (P 3).toNat+(P 4).toNat

def midpointStepSlope (P : Fin 5 → Bool) : ℝ := 2*(stepMiddle P:ℝ)-(stepLeft P:ℝ)-(stepRight P:ℝ)

def midpointStepOffset (P : Fin 5 → Bool) : ℝ :=
  2*(stepMiddle P:ℝ)*Real.log 3-(stepLeft P:ℝ)*Real.log 2-(stepRight P:ℝ)*Real.log 4

/-- Ordinary-prime weight at a single positive integer. -/
def midpointPrimeSiteLog (k : ℕ) := if k.Prime then Real.log k else 0

private theorem log_site_vanishes {d k : ℕ} (hd : 1<d) (hk : d<k) (hdk : d∣k) : midpointPrimeSiteLog k=0 := by
  apply if_neg
  intro hp
  exact hk.ne' ((hp.dvd_iff_eq hd.ne').mp hdk)

/-- Exact increment at each positive center. No approximation of a
prime count or logarithm enters this identity. -/
theorem prime_midpoint_step_five_sites {n : ℕ} (hn : 0<n) :
    primeMidpointStep n=2*(midpointPrimeSiteLog (3*n+1)+midpointPrimeSiteLog (3*n+2))-midpointPrimeSiteLog (2*n+1)-
      midpointPrimeSiteLog (4*n+1)-midpointPrimeSiteLog (4*n+3) := by
  have h (k : ℕ) : Chebyshev.theta (k+1:ℕ)=Chebyshev.theta k+midpointPrimeSiteLog (k+1) :=
    _root_.RHTower.PrimeDeletion.theta_natCast_succ k
  have h₂ := h (2*n)
  have h₂' := h (2*n+1)
  have h₃ := h (3*n)
  have h₃' := h (3*n+1)
  have h₃'' := h (3*n+2)
  have h₄ := h (4*n)
  have h₄' := h (4*n+1)
  have h₄'' := h (4*n+2)
  have h₄''' := h (4*n+3)
  have z₂ := log_site_vanishes (d:=2) (k:=2*n+2) (by decide) (by omega) (by omega)
  have z₃ := log_site_vanishes (d:=3) (k:=3*n+3) (by decide) (by omega) (by omega)
  have z₄ := log_site_vanishes (d:=2) (k:=4*n+2) (by decide) (by omega) (by omega)
  have z₄' := log_site_vanishes (d:=2) (k:=4*n+4) (by decide) (by omega) (by omega)
  simp only [primeMidpointStep,prime_midpoint_price_eq,Nat.mul_add,Nat.mul_one]
  linarith only [h₂,h₂',h₃,h₃',h₃'',h₄,h₄',h₄'',h₄''',z₂,z₃,z₄,z₄']

private theorem log_affine_minus_log {k : ℕ} (hk : 0<k) (r : ℕ) :
    Tendsto (fun n : ℕ => Real.log (k*n+r:ℕ)-Real.log n) atTop (𝓝 (Real.log k)) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (r:ℝ)
  have hv := hi.const_add (k:ℝ)
  simp only [mul_zero,add_zero] at hv
  apply ((Real.continuousAt_log (Nat.cast_ne_zero.mpr hk.ne')).tendsto.comp hv).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn₀ : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hh : ((k*n+r:ℕ):ℝ)≠0 := Nat.cast_ne_zero.mpr (by positivity)
  change Real.log ((k:ℝ)+(r:ℝ)*(n:ℝ)⁻¹)=_
  rw [←Real.log_div hh hn₀]
  congr 1
  push_cast
  field_simp [hn₀]

/-- The exact constant term on any fixed five-site pattern, including
patterns observed along sparse increasing subsequences. -/
theorem prime_midpoint_step_on_a_pattern (P : Fin 5 → Bool) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (h : ∀ j, midpointStepPattern (φ j)=P) :
    Tendsto (fun j => primeMidpointStep (φ j)-midpointStepSlope P*Real.log (φ j))
      atTop (𝓝 (midpointStepOffset P)) := by
  let b := fun i : Fin 5 => ((P i).toNat:ℝ)
  have lim (i : Fin 5) (k r : ℕ) (hk : 0<k) :=
    ((log_affine_minus_log hk r).comp hφ).const_mul (b i)
  have hlim := (((((lim 0 3 1 (by decide)).add (lim 1 3 2 (by decide))).const_mul 2).sub
    (lim 2 2 1 (by decide))).sub (lim 3 4 1 (by decide))).sub (lim 4 4 3 (by decide))
  have hid (j : ℕ) (k : ℕ) (i : Fin 5) (hi : decide k.Prime=midpointStepPattern (φ j) i) :
      midpointPrimeSiteLog k=b i*Real.log k := by
    rw [h j] at hi
    dsimp only [b,midpointPrimeSiteLog]
    rw [←hi]
    by_cases hp : k.Prime <;> simp [hp]
  have hoff : midpointStepOffset P=2*(b 0*Real.log 3+b 1*Real.log 3)-b 2*Real.log 2-b 3*Real.log 4-b 4*Real.log 4 := by
    simp only [midpointStepOffset,stepMiddle,stepLeft,stepRight,b,Nat.cast_add]
    ring
  rw [hoff]
  apply hlim.congr'
  filter_upwards [hφ.eventually_gt_atTop 0] with j hj
  rw [prime_midpoint_step_five_sites hj,hid j _ 0 rfl,hid j _ 1 rfl,hid j _ 2 rfl,hid j _ 3 rfl,hid j _ 4 rfl]
  simp only [Function.comp_apply,midpointStepSlope,stepMiddle,stepLeft,stepRight,b,Nat.cast_add]
  ring

/-- A finite cluster value occurs exactly when a recurring pattern loses
its log n drift and has that value as its constant term. -/
theorem finite_prime_midpoint_step_limit_iff (c : ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun j => primeMidpointStep (φ j)) atTop (𝓝 c)) ↔
    ∃ P : Fin 5 → Bool, (∃ᶠ n : ℕ in atTop, midpointStepPattern n=P) ∧
      midpointStepSlope P=0 ∧ midpointStepOffset P=c := by
  classical
  constructor
  · rintro ⟨φ,hφ,hl⟩
    have hrep : ∃ P : Fin 5 → Bool, ∃ᶠ j : ℕ in atTop, midpointStepPattern (φ j)=P := by
      by_contra! hn
      obtain ⟨j,hj⟩ := (eventually_all.mpr hn).exists
      exact hj _ rfl
    obtain ⟨P,hP⟩ := hrep
    obtain ⟨u,hu,he⟩ := extraction_of_frequently_atTop hP
    have ht := hφ.tendsto_atTop.comp hu.tendsto_atTop
    have hres := prime_midpoint_step_on_a_pattern P ht he
    have hval := hl.comp hu.tendsto_atTop
    have hs : midpointStepSlope P=0 := by
      by_contra hz
      have hdiv := (hval.sub hres).div_const (midpointStepSlope P)
      have hlog : Tendsto (fun j => Real.log (φ (u j))) atTop (𝓝 ((c-midpointStepOffset P)/midpointStepSlope P)) := by
        apply hdiv.congr
        intro j
        change (primeMidpointStep (φ (u j))-(primeMidpointStep (φ (u j))-midpointStepSlope P*Real.log (φ (u j))))/
          midpointStepSlope P=_
        field_simp [hz]
        ring
      exact not_tendsto_nhds_of_tendsto_atTop
        (Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp ht)) _ hlog
    refine ⟨P,frequently_atTop.mpr (fun N => ?_),hs,?_⟩
    · obtain ⟨j,hj⟩ := (ht.eventually_ge_atTop N).exists
      exact ⟨φ (u j),hj,he j⟩
    · exact tendsto_nhds_unique
        (show Tendsto (fun j => primeMidpointStep (φ (u j))) atTop (𝓝 (midpointStepOffset P)) by
          simpa only [Function.comp_apply,hs,zero_mul,sub_zero] using hres) hval
  · rintro ⟨P,hP,hs,rfl⟩
    obtain ⟨φ,hφ,he⟩ := extraction_of_frequently_atTop hP
    exact ⟨φ,hφ,by simpa only [hs,zero_mul,sub_zero] using prime_midpoint_step_on_a_pattern P hφ.tendsto_atTop he⟩

private theorem side_counts {P : Fin 5 → Bool} (hf : ∃ᶠ n : ℕ in atTop, midpointStepPattern n=P) :
    stepMiddle P≤1 ∧ stepLeft P≤1 ∧ stepRight P≤2 := by
  obtain ⟨n,hP,hn⟩ := (hf.and_eventually (eventually_ge_atTop 1)).exists
  have even_off {k : ℕ} (hk : 2<k) (hd : 2∣k) : ¬k.Prime :=
    fun hp => hk.ne' ((hp.dvd_iff_eq (by decide : 2≠1)).mp hd)
  have hno : ¬((3*n+1).Prime ∧ (3*n+2).Prime) := by
    rintro ⟨h₁,h₂⟩
    by_cases hd : 2∣3*n+1
    · exact even_off (by omega) hd h₁
    · exact even_off (by omega) (by omega) h₂
  have hbit (v : Bool) : v.toNat≤1 := by cases v <;> decide
  have hmid : stepMiddle P≤1 := by
    rw [←hP]
    change (decide (3*n+1).Prime).toNat+(decide (3*n+2).Prime).toNat≤1
    by_cases h₁ : (3*n+1).Prime <;> by_cases h₂ : (3*n+2).Prime <;> simp_all
  exact ⟨hmid,hbit _,Nat.add_le_add (hbit (P 3)) (hbit (P 4))⟩

/-- Every finite subsequential limit of the first midpoint difference
belongs to the displayed three-element set. The middle-left-right triple
gives log(9/8); the middle-right-right triple gives log(9/16). -/
theorem three_possible_finite_prime_midpoint_steps {c : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h : Tendsto (fun j => primeMidpointStep (φ j)) atTop (𝓝 c)) :
    c=0 ∨ c=Real.log (9/8:ℝ) ∨ c=Real.log (9/16:ℝ) := by
  obtain ⟨P,hP,hs,rfl⟩ := (finite_prime_midpoint_step_limit_iff c).mp ⟨φ,hφ,h⟩
  obtain ⟨hm,hl,hr⟩ := side_counts hP
  have he : 2*stepMiddle P=stepLeft P+stepRight P := by
    exact_mod_cast (show 2*(stepMiddle P:ℝ)=(stepLeft P:ℝ)+(stepRight P:ℝ) by
      dsimp only [midpointStepSlope] at hs; linarith only [hs])
  have hc : (stepMiddle P=0 ∧ stepLeft P=0 ∧ stepRight P=0) ∨
      (stepMiddle P=1 ∧ stepLeft P=1 ∧ stepRight P=1) ∨ (stepMiddle P=1 ∧ stepLeft P=0 ∧ stepRight P=2) := by omega
  have h₉ : Real.log 9=2*Real.log 3 := by rw [show (9:ℝ)=3^2 by norm_num,Real.log_pow]; norm_num
  rcases hc with ⟨a,b,d⟩ | ⟨a,b,d⟩ | ⟨a,b,d⟩
  · exact Or.inl (by simp [midpointStepOffset,a,b,d])
  · refine Or.inr (Or.inl ?_)
    rw [Real.log_div (by norm_num) (by norm_num),h₉,
      show (8:ℝ)=2*4 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    simp only [midpointStepOffset,a,b,d,Nat.cast_one]
    ring
  · refine Or.inr (Or.inr ?_)
    rw [Real.log_div (by norm_num) (by norm_num),h₉,show (16:ℝ)=4^2 by norm_num,Real.log_pow]
    simp only [midpointStepOffset,a,b,d,Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat]
    ring

/-- Every center congruent to two modulo 2310, past two itself, has
an exactly zero jump because each candidate has a fixed small divisor. -/
theorem vanishing_prime_midpoint_step_progression (j : ℕ) : primeMidpointStep (2310*(j+1)+2)=0 := by
  let n := 2310*(j+1)+2
  change primeMidpointStep n=0
  rw [prime_midpoint_step_five_sites (by dsimp only [n]; omega)]
  have h₁ := log_site_vanishes (d:=7) (k:=3*n+1) (by decide) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have h₂ := log_site_vanishes (d:=2) (k:=3*n+2) (by decide) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have h₃ := log_site_vanishes (d:=5) (k:=2*n+1) (by decide) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have h₄ := log_site_vanishes (d:=3) (k:=4*n+1) (by decide) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have h₅ := log_site_vanishes (d:=11) (k:=4*n+3) (by decide) (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  rw [h₁,h₂,h₃,h₄,h₅]
  ring

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
