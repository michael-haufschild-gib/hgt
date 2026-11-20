import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheOrderOfAbsoluteMertensMass
import GaloisForLFunctions.RHTower.MobiusMertensMeanSquareExponentLaw

/-!
# The right-endpoint quadrature error of absolute Mertens mass

Give index k the normalized weight proportional to |M(k)|/k. Its mean
cumulative rank exceeds 1/2 by exactly half the sum of squared weights.
The collision probability is N^(-1+o(1)) regardless of the zero abscissa.
Consequently any set of polynomially sublinear cardinality carries a
vanishing share, even if its positions are chosen after observing the weights.
-/

noncomputable section
open Filter Finset Topology
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

def mertensAbelJump (j : ℕ) : ℝ := ‖mobiusMertensPartialSum (j+1)‖/((j:ℝ)+1)

def mertensAbelCollision (N : ℕ) : ℝ :=
  (∑ j ∈ range N,mertensAbelJump j^2)/(mertensAbelMass N)^2

private theorem jump_nonneg (j : ℕ) : 0 ≤ mertensAbelJump j :=
  div_nonneg (norm_nonneg _) (by positivity)

private theorem abel_mass_succ (n : ℕ) :
    mertensAbelMass (n+1) = mertensAbelMass n + mertensAbelJump n :=
  Finset.sum_range_succ _ _

/-- Discrete change of variables for the identity function. -/
theorem cumulative_mertens_quadrature (N : ℕ) :
    2*∑ j ∈ range N,mertensAbelJump j*mertensAbelMass (j+1) =
      mertensAbelMass N^2 + ∑ j ∈ range N,mertensAbelJump j^2 := by
  induction N with
  | zero => simp [mertensAbelMass]
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ (f:=fun j => mertensAbelJump j^2),
      abel_mass_succ,mul_add,ih]
    ring

private theorem collision_numerator_upper {a : ℝ} (ha : zetaZeroAbscissa<a) :
    ∃ B : ℝ, 0≤B ∧ ∀ N, (∑ j ∈ range N, mertensAbelJump j^2) ≤ B*((N:ℝ)+1)^(2*a-1) := by
  have hv : 0<2*a-1 := by linarith only [half_le_zetaZeroAbscissa,ha]
  have ha0 : 0≤a := by linarith only [hv]
  obtain ⟨A,hA,hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
  rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa)=a by ring] at hM
  let C := A*2^a
  have hC : 0≤C := mul_nonneg hA (by positivity)
  refine ⟨C^2*(1+1/(2*a-1)),by positivity,fun N => ?_⟩
  have row (j : ℕ) : mertensAbelJump j^2 ≤ C^2*((j:ℝ)+1)^((2*a-1)-1) := by
    let x := (j:ℝ)+1
    have h1 : 1≤x := le_add_of_nonneg_left (Nat.cast_nonneg j)
    have xp := zero_lt_one.trans_le h1
    have h := hM (j+1)
    rw [Nat.cast_succ] at h
    have hp := Real.rpow_le_rpow (by positivity : 0≤x+1) (by linarith only [h1] : x+1≤2*x) ha0
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) xp.le] at hp
    have hj : mertensAbelJump j ≤ C*x^(a-1) := by
      change ‖mobiusMertensPartialSum (j+1)‖/x ≤ C*x^(a-1)
      apply (div_le_iff₀ xp).mpr
      rw [Real.rpow_sub xp,Real.rpow_one]
      exact (h.trans (mul_le_mul_of_nonneg_left hp hA)).trans_eq (by dsimp only [C]; field_simp)
    have hs := pow_le_pow_left₀ (jump_nonneg j) hj 2
    rw [mul_pow,←Real.rpow_two (x^(a-1)),←Real.rpow_mul xp.le] at hs
    rwa [show (a-1)*2=(2*a-1)-1 by ring] at hs
  have hs := sum_le_sum (s:=range N) (fun j _ => row j)
  rw [←mul_sum] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (ArithmeticGaugeTheory.sum_rpow_sub_one_le hv N)
    (sq_nonneg C)).trans_eq (by ring))

/-- Exact attainable lower scale, and an upper bound within any positive
power of it, for the collision probability of normalized Mertens mass. -/
theorem mertens_collision_exponent {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ N : ℕ in atTop,
      1/(N:ℝ) ≤ mertensAbelCollision N ∧ mertensAbelCollision N ≤ B*((N:ℝ)+1)^(-1+ε) := by
  let d := min (ε/4) (zetaZeroAbscissa/2)
  have hΘ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  have hd : 0<d := lt_min (by positivity) (half_pos hΘ)
  let a := zetaZeroAbscissa+d
  let b := zetaZeroAbscissa-d
  have hb0 : 0≤b := by dsimp only [b,d]; linarith only [min_le_right (ε/4) (zetaZeroAbscissa/2),hΘ]
  have hba : b<zetaZeroAbscissa := sub_lt_self _ hd
  obtain ⟨B,hB,hcap⟩ := collision_numerator_upper (a:=a) (lt_add_of_pos_right _ hd)
  refine ⟨B,hB,?_⟩
  filter_upwards [eventually_large_mertens_abel_mass hb0 hba 1,eventually_ge_atTop 1] with N h hn
  let X := (N:ℝ)+1
  have hX : 1≤X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have xp := zero_lt_one.trans_le hX
  rw [one_mul] at h
  have hm := (Real.rpow_pos_of_pos xp b).trans h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg xp.le b) h.le 2
  rw [←Real.rpow_two (X^b),←Real.rpow_mul xp.le] at hp
  have he : 2*a-1-b*2 ≤ -1+ε := by
    dsimp only [a,b,d]; linarith only [min_le_left (ε/4) (zetaZeroAbscissa/2)]
  constructor
  · have hc := sq_sum_mul_le_sum_sq_mul_mul_sum (range N) mertensAbelJump (fun _ => 1) (fun _ _ => zero_le_one)
    simp only [mul_one,sum_const,card_range,nsmul_eq_mul] at hc
    exact (div_le_div_iff₀ (Nat.cast_pos.mpr hn) (sq_pos_of_pos hm)).mpr (by
      change 1*(∑ j ∈ range N,mertensAbelJump j)^2 ≤ _
      linarith only [hc])
  · apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    calc _ ≤ B*X^(2*a-1) := hcap N
         _ = (B*X^(2*a-1-b*2))*X^(b*2) := by rw [mul_assoc,←Real.rpow_add xp,sub_add_cancel]
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX he) hB)
            hp (Real.rpow_nonneg xp.le _) (mul_nonneg hB (Real.rpow_nonneg xp.le _))

/-- Squared mass share of any subset is bounded by its size times the
collision probability of the entire section. -/
theorem mertens_mass_share_le_card_collision (N : ℕ) (S : Finset ℕ) (hS : S ⊆ range N) :
    ((∑ j ∈ S,mertensAbelJump j)/mertensAbelMass N)^2 ≤ S.card*mertensAbelCollision N := by
  have hc := sq_sum_mul_le_sum_sq_mul_mul_sum S mertensAbelJump (fun _ => 1) (fun _ _ => zero_le_one)
  simp only [mul_one,sum_const,nsmul_eq_mul] at hc
  have hs := sum_le_sum_of_subset_of_nonneg (f:=fun j => mertensAbelJump j^2) hS (fun j _ _ => sq_nonneg _)
  rw [div_pow,mertensAbelCollision,←mul_div_assoc]
  exact div_le_div_of_nonneg_right (hc.trans ((mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg S.card)).trans_eq
    (mul_comm _ _))) (sq_nonneg _)

/-- Even the most heavily weighted set of at most N^g positions, g<1,
carries asymptotically none of the normalized absolute mass. -/
theorem polynomially_sparse_mertens_share_vanishes (S : ℕ → Finset ℕ) {g : ℝ} (hg : g<1)
    (hS : ∀ N, S N ⊆ range N) (hs : ∀ᶠ N : ℕ in atTop, ((S N).card:ℝ) ≤ ((N:ℝ)+1)^g) :
    Tendsto (fun N => (∑ j ∈ S N,mertensAbelJump j)/mertensAbelMass N) atTop (𝓝 0) := by
  let e := (1-g)/2
  have he : 0<e := half_pos (sub_pos.mpr hg)
  obtain ⟨B,hB,hh⟩ := mertens_collision_exponent he
  have hX : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hl := (tendsto_rpow_neg_atTop he).comp hX
  have hz : Tendsto (fun N : ℕ => B*((N:ℝ)+1)^(-e)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hl.const_mul B
  have hsq : Tendsto (fun N => ((∑ j ∈ S N,mertensAbelJump j)/mertensAbelMass N)^2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
    · exact .of_forall fun _ => sq_nonneg _
    · filter_upwards [hs,hh] with N nh ch
      let X := (N:ℝ)+1
      have xp : 0<X := by dsimp only [X]; positivity
      have hc : 0≤mertensAbelCollision N := div_nonneg (sum_nonneg fun j _ => sq_nonneg _) (sq_nonneg _)
      apply (mertens_mass_share_le_card_collision N (S N) (hS N)).trans
      calc _ ≤ X^g * (B*X^(-1+e)) := mul_le_mul nh ch.2 hc (Real.rpow_nonneg xp.le _)
           _ = B*X^(-e) := by rw [mul_left_comm,←Real.rpow_add xp]; congr 2; dsimp only [e]; ring
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (div_nonneg (sum_nonneg fun j _ => jump_nonneg j)
    (mertens_abel_mass_nonneg _)),Real.sqrt_zero] using h

#print axioms cumulative_mertens_quadrature
#print axioms mertens_collision_exponent
#print axioms polynomially_sparse_mertens_share_vanishes
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
