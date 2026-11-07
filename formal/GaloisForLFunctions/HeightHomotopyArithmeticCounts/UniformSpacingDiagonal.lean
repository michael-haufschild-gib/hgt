import GaloisForLFunctions.HeightHomotopyArithmeticCounts.SharpTorsionChordBounds
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.ConductorControlledRegularization
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheSpacingRegulatorRemovesTheAnomaly

/-!
# Conductor-uniform diagonal renormalization

At the arithmetic spacing radius `exp(-2ε/n)`, the exact full-root chord
energy controls the radial remainder uniformly after totient normalization.
The existing scalar-counterterm limit to the tame different has the uniform
modulus `max(3ε, ε² exp(2ε)/6)`, independent of the positive conductor.
The same modulus bounds the diagonal quadratic form on every finite set.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts


/-- The spacing radius has a conductor-scaled quadratic displacement. -/
theorem spacing_scalar_bounds (ε N : ℝ) (hε : 0<ε) (hN : 1≤N) :
    0 < Real.exp (-(2*ε/N)) ∧ Real.exp (-(2*ε/N)) < 1 ∧
    (1-Real.exp (-(2*ε/N)))^2*N^2 ≤ 4*ε^2 ∧
    (Real.exp (-(2*ε/N)))⁻¹ ≤ Real.exp (2*ε) := by
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hu : 0<2*ε/N := div_pos (mul_pos (by norm_num) hε) hN0
  have hr0 := Real.exp_pos (-(2*ε/N))
  have hr1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  have hδ : 0≤1-Real.exp (-(2*ε/N)) := sub_nonneg.mpr hr1.le
  have hδN : (1-Real.exp (-(2*ε/N)))*N ≤ 2*ε := by
    apply (le_div_iff₀ hN0).mp
    have h := Real.add_one_le_exp (-(2*ε/N))
    linarith only [h]
  have hs := mul_le_mul hδN hδN (mul_nonneg hδ hN0.le)
    (show 0≤2*ε by positivity)
  refine ⟨hr0, hr1, ?_, ?_⟩
  · nlinarith only [hs]
  · rw [← Real.exp_neg, neg_neg]
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hN0).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hN (show 0≤2*ε by positivity)

/-- The scalar counterterm differs from the actual radial logarithm by at most its scale. -/
theorem spacing_log_defect_bounds (u : ℝ) (hu : 0<u) :
    0 ≤ Real.log u-Real.log (1-Real.exp (-u)) ∧
    Real.log u-Real.log (1-Real.exp (-u)) ≤ u := by
  have hs : 0<1-Real.exp (-u) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hupper : 1-Real.exp (-u)≤u := by
    have h := Real.add_one_le_exp (-u)
    linarith only [h]
  have hlower : u*Real.exp (-u)≤1-Real.exp (-u) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) (Real.exp_pos (-u)).le
    have he : Real.exp (-u)*Real.exp u=1 := by rw [← Real.exp_add]; simp
    rw [he] at h
    nlinarith only [h]
  constructor
  · have h := Real.log_le_log hs hupper
    linarith only [h]
  · have h := Real.log_le_log (mul_pos hu (Real.exp_pos (-u))) hlower
    rw [Real.log_mul hu.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    linarith only [h]

open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

private theorem spacingRadius_self_eq (ε : ℝ) (n : ℕ) :
    spacingRadius ε n n = Real.exp (-(2*ε/n)) := by
  rw [spacingRadius]
  congr 1
  ring

/-- At the arithmetic spacing radius, the normalized radial remainder is conductor-uniform. -/
theorem spacing_diagonal_remainder_uniform (ε : Set.Ioi (0:ℝ)) (n : ℕ) :
    torsionRadialError (spacingRadius ε (n+1) (n+1)) (n+1) (n+1) ≤
      (Nat.totient (n+1):ℝ)*((ε:ℝ)^2*Real.exp (2*ε)/6) := by
  let N := n+1
  let r := spacingRadius ε N N
  have hr : r=Real.exp (-(2*ε/(N:ℝ))) := spacingRadius_self_eq ε N
  have hN1 : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hb := spacing_scalar_bounds ε N ε.property hN1
  have hr0 : 0<r := by rw [hr]; exact hb.1
  have hs : (1-r)^2*(N:ℝ)^2≤4*(ε:ℝ)^2 := by rw [hr]; exact hb.2.2.1
  have hi : r⁻¹≤Real.exp (2*ε) := by rw [hr]; exact hb.2.2.2
  have hφ : 0≤(Nat.totient N:ℝ) := Nat.cast_nonneg _
  change torsionRadialError r N N ≤ (Nat.totient N:ℝ)*((ε:ℝ)^2*Real.exp (2*ε)/6)
  calc
    torsionRadialError r N N ≤ (1-r)^2*(Nat.totient N:ℝ)*((N:ℝ)^2-1)/(24*r) :=
      torsionRadialError_self_sharp r hr0 N
    _ ≤ (1-r)^2*(Nat.totient N:ℝ)*(N:ℝ)^2/(24*r) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (mul_nonneg (sq_nonneg _) hφ)
    _ = ((Nat.totient N:ℝ)/24)*((1-r)^2*(N:ℝ)^2*r⁻¹) := by ring
    _ ≤ ((Nat.totient N:ℝ)/24)*(4*(ε:ℝ)^2*Real.exp (2*ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hs hi (inv_nonneg.mpr hr0.le) (by positivity)) (by positivity)
    _ = (Nat.totient N:ℝ)*((ε:ℝ)^2*Real.exp (2*ε)/6) := by ring

/-- The regularized self-energy lies between a quadratic negative error and a linear positive error. -/
theorem spacing_self_energy_bounds (ε : Set.Ioi (0:ℝ)) (n : ℕ) :
    -((Nat.totient (n+1):ℝ)*((ε:ℝ)^2*Real.exp (2*ε)/6)) ≤
      spacingEnergy ε (n+1) (n+1) + (Nat.totient (n+1):ℝ)*
        Real.log (1-spacingRadius ε (n+1) (n+1)) + orbitIntersection (n+1) (n+1) ∧
    spacingEnergy ε (n+1) (n+1) + (Nat.totient (n+1):ℝ)*
        Real.log (1-spacingRadius ε (n+1) (n+1)) + orbitIntersection (n+1) (n+1) ≤
      (Nat.totient (n+1):ℝ)*ε := by
  let N := n+1
  let r := spacingRadius ε N N
  let E := (ε:ℝ)^2*Real.exp (2*ε)/6
  have hN0 : (0:ℝ)<N := by exact_mod_cast Nat.succ_pos n
  have hr0 : 0<r := Real.exp_pos _
  have hr1 : r<1 := spacingRadius_lt_one ε.property (Nat.succ_pos n)
  have hlog : Real.log r=-(2*ε/(N:ℝ)) := by
    change Real.log (spacingRadius ε N N)=-(2*ε/(N:ℝ))
    rw [spacingRadius_self_eq, Real.log_exp]
  have hdecomp := torsionEnergy_finite_radius r hr0 N
  rw [abs_of_pos (sub_pos.mpr hr1), hlog] at hdecomp
  have hD : torsionEnergy r N N + (Nat.totient N:ℝ)*Real.log (1-r) + orbitIntersection N N =
      (ε:ℝ)*(torsionPairCount N N:ℝ)/N-torsionRadialError r N N := by
    linear_combination hdecomp
  have hcNat : torsionPairCount N N ≤ Nat.totient N * N := by
    rw [torsionPairCount_self]
    exact Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (Nat.totient_le N))
  have hc : (torsionPairCount N N:ℝ)≤(Nat.totient N:ℝ)*(N:ℝ) := by exact_mod_cast hcNat
  have hB0 : 0≤(ε:ℝ)*(torsionPairCount N N:ℝ)/N :=
    div_nonneg (mul_nonneg ε.property.le (Nat.cast_nonneg _)) hN0.le
  have hB : (ε:ℝ)*(torsionPairCount N N:ℝ)/N≤(Nat.totient N:ℝ)*ε := by
    apply (div_le_iff₀ hN0).mpr
    calc (ε:ℝ)*(torsionPairCount N N:ℝ) ≤ (ε:ℝ)*((Nat.totient N:ℝ)*(N:ℝ)) :=
        mul_le_mul_of_nonneg_left hc ε.property.le
      _ = ((Nat.totient N:ℝ)*ε)*N := by ring
  have hR0 := (torsionRadialError_bounds r hr0 N N).1
  have hR : torsionRadialError r N N≤(Nat.totient N:ℝ)*E :=
    spacing_diagonal_remainder_uniform ε n
  change -((Nat.totient N:ℝ)*E) ≤
      torsionEnergy r N N + (Nat.totient N:ℝ)*Real.log (1-r) + orbitIntersection N N ∧
    torsionEnergy r N N + (Nat.totient N:ℝ)*Real.log (1-r) + orbitIntersection N N ≤
      (Nat.totient N:ℝ)*ε
  rw [hD]
  constructor <;> linarith only [hB0, hB, hR0, hR]

/-- A conductor-uniform modulus after removing the coincident-point self-energy. -/
theorem spacing_self_energy_uniform (ε : Set.Ioi (0:ℝ)) (n : ℕ) :
    |spacingEnergy ε (n+1) (n+1) + (Nat.totient (n+1):ℝ)*
      Real.log (1-spacingRadius ε (n+1) (n+1)) + orbitIntersection (n+1) (n+1)| ≤
    (Nat.totient (n+1):ℝ)*max (ε:ℝ) ((ε:ℝ)^2*Real.exp (2*ε)/6) := by
  have hb := spacing_self_energy_bounds ε n
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left
      (le_max_right (ε:ℝ) ((ε:ℝ)^2*Real.exp (2*ε)/6)) (Nat.cast_nonneg (Nat.totient (n+1)))
    linarith only [hb.1, hm]
  · exact hb.2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg (Nat.totient (n+1))))

/-- The scalar-counterterm limit is uniform over every positive torsion conductor. -/
theorem spacing_diagonal_uniform (ε : Set.Ioi (0:ℝ)) (n : ℕ) :
    |twistedEnergy (spacingRadius ε (n+1) (n+1)) (n+1) (n+1) +
      Real.log (2*ε)-tameDifferent (n+1)| ≤
    max (3*(ε:ℝ)) ((ε:ℝ)^2*Real.exp (2*ε)/6) := by
  let N := n+1
  let r := spacingRadius ε N N
  let u := 2*(ε:ℝ)/(N:ℝ)
  let E := (ε:ℝ)^2*Real.exp (2*ε)/6
  let D := spacingEnergy ε N N + (Nat.totient N:ℝ)*Real.log (1-r) + orbitIntersection N N
  have hN0 : (0:ℝ)<N := by exact_mod_cast Nat.succ_pos n
  have hN1 : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hφ : (0:ℝ)<Nat.totient N := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos n)
  have hu : 0<u := div_pos (mul_pos (by norm_num) ε.property) hN0
  have huupper : u≤2*(ε:ℝ) := by
    apply (div_le_iff₀ hN0).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hN1 (mul_nonneg (by norm_num) ε.property.le)
  have hr : r=Real.exp (-u) := spacingRadius_self_eq ε N
  have hb := spacing_self_energy_bounds ε n
  change -((Nat.totient N:ℝ)*E)≤D ∧ D≤(Nat.totient N:ℝ)*ε at hb
  have hdlo : -E≤D/(Nat.totient N:ℝ) := by
    apply (le_div_iff₀ hφ).mpr
    nlinarith only [hb.1]
  have hdup : D/(Nat.totient N:ℝ)≤ε := by
    apply (div_le_iff₀ hφ).mpr
    nlinarith only [hb.2]
  have hlog := spacing_log_defect_bounds u hu
  rw [← hr] at hlog
  have hlogu : Real.log u=Real.log (2*(ε:ℝ))-Real.log N :=
    Real.log_div (mul_pos (by norm_num) ε.property).ne' hN0.ne'
  have hself : orbitIntersection N N/(Nat.totient N:ℝ)=Real.log N-tameDifferent N := by
    have h := selfIntersection_eq (Nat.succ_pos n)
    simpa only [selfIntersection] using h
  have hdiag : twistedEnergy r N N=torsionEnergy r N N/(Nat.totient N:ℝ) := by
    rw [twistedEnergy, gcdTwist_eq, Nat.gcd_self, Real.sqrt_mul_self hN0.le]
    field_simp
  have hcancel : (Nat.totient N:ℝ)*Real.log (1-r)/(Nat.totient N:ℝ)=Real.log (1-r) := by
    field_simp [hφ.ne']
  have hDiv : D/(Nat.totient N:ℝ)=torsionEnergy r N N/(Nat.totient N:ℝ)+
      Real.log (1-r)+Real.log N-tameDifferent N := by
    change (torsionEnergy r N N+(Nat.totient N:ℝ)*Real.log (1-r)+orbitIntersection N N)/
      (Nat.totient N:ℝ)=_
    rw [add_div, add_div, hcancel, hself]
    ring
  have heq : twistedEnergy r N N+Real.log (2*(ε:ℝ))-tameDifferent N =
      D/(Nat.totient N:ℝ)+(Real.log u-Real.log (1-r)) := by
    rw [hdiag, hDiv, hlogu]
    ring
  change |twistedEnergy r N N+Real.log (2*(ε:ℝ))-tameDifferent N| ≤ max (3*(ε:ℝ)) E
  rw [heq]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hm := le_max_right (3*(ε:ℝ)) E
    linarith only [hdlo, hlog.1, hm]
  · have hm := le_max_left (3*(ε:ℝ)) E
    linarith only [hdup, hlog.2, huupper, hm]

/-- The diagonal error has a uniform quadratic-form bound on every finite conductor set. -/
theorem spacing_diagonal_quadratic_bound (ε : Set.Ioi (0:ℝ)) (S : Finset ℕ) (x : ℕ → ℝ) :
    |∑ n ∈ S, (x n)^2*(twistedEnergy (spacingRadius ε (n+1) (n+1)) (n+1) (n+1)+
      Real.log (2*ε)-tameDifferent (n+1))| ≤
    max (3*(ε:ℝ)) ((ε:ℝ)^2*Real.exp (2*ε)/6) * ∑ n ∈ S, (x n)^2 := by
  calc
    |∑ n ∈ S, (x n)^2*(twistedEnergy (spacingRadius ε (n+1) (n+1)) (n+1) (n+1)+
        Real.log (2*ε)-tameDifferent (n+1))| ≤
      ∑ n ∈ S, |(x n)^2*(twistedEnergy (spacingRadius ε (n+1) (n+1)) (n+1) (n+1)+
        Real.log (2*ε)-tameDifferent (n+1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ max (3*(ε:ℝ)) ((ε:ℝ)^2*Real.exp (2*ε)/6)*∑ n ∈ S, (x n)^2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro n _hn
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc (x n)^2*|twistedEnergy (spacingRadius ε (n+1) (n+1)) (n+1) (n+1)+
          Real.log (2*ε)-tameDifferent (n+1)| ≤
          (x n)^2*max (3*(ε:ℝ)) ((ε:ℝ)^2*Real.exp (2*ε)/6) :=
            mul_le_mul_of_nonneg_left (spacing_diagonal_uniform ε n) (sq_nonneg _)
        _ = max (3*(ε:ℝ)) ((ε:ℝ)^2*Real.exp (2*ε)/6)*(x n)^2 := by ring

#print axioms spacing_diagonal_remainder_uniform
#print axioms spacing_self_energy_uniform
#print axioms spacing_diagonal_uniform
#print axioms spacing_diagonal_quadratic_bound

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
