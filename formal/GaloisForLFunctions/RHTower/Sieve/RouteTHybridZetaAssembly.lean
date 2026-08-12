import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaHead
import GaloisForLFunctions.RHTower.Sieve.RouteTHybridZetaBlock

/-!
# Dyadic assembly of the hybrid Route-T receiver

The natural endpoint convention for Route T is `(X,2X]`.  These blocks partition an inclusive
zeta partial sum exactly, so no endpoint loss is accumulated.  A single external shell index and
one threshold at the first block certify every later block.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The even floor-root base is monotone in its centre. -/
theorem routeTLogRootBase_mono {X Y : ℕ} (hXY : X ≤ Y) :
    routeTLogRootBase X ≤ routeTLogRootBase Y := by
  have hdegree : routeTLogCentreExponent ≠ 0 := by
    norm_num [routeTLogCentreExponent]
  have hroot : Nat.nthRoot routeTLogCentreExponent X ≤
      Nat.nthRoot routeTLogCentreExponent Y := by
    apply (Nat.le_nthRoot_iff hdegree).2
    exact (Nat.pow_nthRoot_le (Or.inl hdegree)).trans hXY
  unfold routeTLogRootBase routeTLogRootHalfBase
  exact Nat.mul_le_mul_left 2 (Nat.div_le_div_right hroot)

/-- A global external shell index turns its degree-nine threshold into the automatic local one. -/
theorem routeT_degreeNine_size_of_externalShell
    {X V : ℕ} {t : ℝ}
    (htop : t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ))
    (hsize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ X) :
    2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant *
        (routeTLogRealShellIndex X t + 1) ^ 9 + 1)) ≤ X := by
  have huv : routeTLogRealShellIndex X t ≤ V := routeTLogRealShellIndex_le htop
  apply (Nat.pow_le_pow_right (by omega) ?_).trans hsize
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (Nat.add_le_add_right huv 1) 9

/-- An external shell upper bound persists when the block centre increases. -/
theorem routeT_externalShell_mono
    {A X V : ℕ} {t : ℝ} (hAX : A ≤ X)
    (htop : t ≤ (((routeTLogRootBase A ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ)) :
    t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ) := by
  have hroot := routeTLogRootBase_mono hAX
  have hcentre : routeTLogRootBase A ^ routeTLogCentreExponent ≤
      routeTLogRootBase X ^ routeTLogCentreExponent :=
    Nat.pow_le_pow_left hroot _
  have hshell :
      (routeTLogRootBase A ^ routeTLogCentreExponent) ^ (4 * V) ≤
        (routeTLogRootBase X ^ routeTLogCentreExponent) ^ (4 * V) :=
    Nat.pow_le_pow_left hcentre _
  exact htop.trans (by exact_mod_cast hshell)

/-- Dyadic decomposition with Route T's endpoint convention. -/
theorem sum_Ioc_dyadic {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) (R : ℕ) :
    ∑ n ∈ Finset.Ioc A (A * 2 ^ R), f n =
      ∑ r ∈ Finset.range R,
        ∑ n ∈ Finset.Ioc (A * 2 ^ r) (A * 2 ^ (r + 1)), f n := by
  induction R with
  | zero => simp
  | succ R ih =>
      have hstart : A ≤ A * 2 ^ R := by
        calc
          A = A * 1 := (Nat.mul_one A).symm
          _ ≤ A * 2 ^ R := Nat.mul_le_mul_left A Nat.one_le_two_pow
      have hmono : A * 2 ^ R ≤ A * 2 ^ (R + 1) := by
        exact Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ioc_consecutive f hstart hmono]

/-- Triangle inequality across exact `(X,2X]` blocks. -/
theorem norm_sum_Ioc_dyadic_le {E : Type*} [NormedAddCommGroup E]
    (A : ℕ) (f : ℕ → E) (R : ℕ) :
    ‖∑ n ∈ Finset.Ioc A (A * 2 ^ R), f n‖ ≤
      ∑ r ∈ Finset.range R,
        ‖∑ n ∈ Finset.Ioc (A * 2 ^ r) (A * 2 ^ (r + 1)), f n‖ := by
  rw [sum_Ioc_dyadic]
  exact norm_sum_le _ _

/-- The pointwise majorant supplied by the automatic hybrid receiver. -/
noncomputable def routeTHybridBlockBound (X : ℕ) (σ t : ℝ) : ℝ :=
  if (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * 141) : ℕ) : ℝ) < t then
    (6912 * Real.exp ((1 - σ) * Real.log (((X + 1 : ℕ) : ℝ)) -
      (1 / (5000000000000000 *
        (routeTLogRealShellIndex X t : ℝ) ^ 4)) *
          (Real.log (X : ℝ) - 200 * Real.log 2)))
  else (2560 * (((X + 1 : ℕ) : ℝ)) ^ (1 - σ) *
      (((X + 1 : ℕ) : ℝ)) ^ (-(1 / (3 * (2 : ℝ) ^ (566 : ℕ)))))

/-- In the hybrid strip, either active branch is bounded by one absolute constant. -/
theorem routeTHybridBlockBound_le
    {X V : ℕ} {σ t : ℝ} (hX : 1 ≤ X) (hσ : σ ≤ 1)
    (hsize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ X)
    (htop : t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ))
    (hroute : 2 * (1 - σ) ≤
      1 / (5000000000000000 * (V : ℝ) ^ 4))
    (hderivative : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ (566 : ℕ))) :
    routeTHybridBlockBound X σ t ≤ 6912 := by
  have hC10 : 10 ≤ routeTLogReceiverDegreeNineConstant := by
    unfold routeTLogReceiverDegreeNineConstant
    omega
  have hVpow : 1 ≤ (V + 1) ^ 9 := Nat.one_le_pow _ _ (by omega)
  have hprod10 : 10 ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 := by
    calc
      10 = 10 * 1 := (Nat.mul_one 10).symm
      _ ≤ routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 :=
        Nat.mul_le_mul hC10 hVpow
  have hexponent : 401 ≤ routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1) := by
    norm_num [routeTLogCentreExponent]
    omega
  have hX401 : 2 ^ (401 : ℕ) ≤ X :=
    (Nat.pow_le_pow_right (by omega) hexponent).trans hsize
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le one_pos hX1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast401 : (((2 ^ (401 : ℕ) : ℕ) : ℝ)) = (2 : ℝ) ^ (401 : ℕ) := by
    norm_cast
  have hlogX : (401 : ℝ) * Real.log 2 ≤ Real.log X := by
    have hcast : (((2 ^ (401 : ℕ) : ℕ) : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hX401
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ (401 : ℕ) : ℕ) : ℝ)) hcast
    rw [hcast401, Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hlogplus : Real.log (((X + 1 : ℕ) : ℝ)) ≤
      2 * (Real.log X - 200 * Real.log 2) := by
    have hcast : ((X + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
      exact_mod_cast (by omega : X + 1 ≤ 2 * X)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((X + 1 : ℕ) : ℝ)) hcast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hlog
    norm_num at hlog ⊢
    linarith
  have hmargin : 0 ≤ Real.log X - 200 * Real.log 2 := by
    linarith
  have htheta : 0 ≤ 1 - σ := by linarith
  by_cases hlarge :
      (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
        (4 * 141) : ℕ) : ℝ) < t
  · rw [routeTHybridBlockBound, if_pos hlarge]
    have hlocalSize := routeT_degreeNine_size_of_externalShell htop hsize
    have hB2 := routeTLogRootBase_ge_two_of_degreeNine_size hlocalSize
    have hu141 : 141 < routeTLogRealShellIndex X t :=
      routeTLogRealShellIndex_ge hB2 hlarge
    have huv : routeTLogRealShellIndex X t ≤ V := routeTLogRealShellIndex_le htop
    have hpowNat : (routeTLogRealShellIndex X t) ^ 4 ≤ V ^ 4 :=
      Nat.pow_le_pow_left huv 4
    have hpowReal : (routeTLogRealShellIndex X t : ℝ) ^ 4 ≤ (V : ℝ) ^ 4 := by
      exact_mod_cast hpowNat
    have hdenpos : 0 < 5000000000000000 *
        (routeTLogRealShellIndex X t : ℝ) ^ 4 := by
      have : (0 : ℝ) < routeTLogRealShellIndex X t := by exact_mod_cast (by omega : 0 < routeTLogRealShellIndex X t)
      positivity
    have hcoeff : 1 / (5000000000000000 * (V : ℝ) ^ 4) ≤
        1 / (5000000000000000 *
          (routeTLogRealShellIndex X t : ℝ) ^ 4) := by
      apply one_div_le_one_div_of_le hdenpos
      gcongr
    have hweight : (1 - σ) * Real.log (((X + 1 : ℕ) : ℝ)) ≤
        (1 / (5000000000000000 *
          (routeTLogRealShellIndex X t : ℝ) ^ 4)) *
            (Real.log X - 200 * Real.log 2) := by
      calc
        (1 - σ) * Real.log (((X + 1 : ℕ) : ℝ)) ≤
            (1 - σ) * (2 * (Real.log X - 200 * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hlogplus htheta
        _ = (2 * (1 - σ)) * (Real.log X - 200 * Real.log 2) := by ring
        _ ≤ (1 / (5000000000000000 * (V : ℝ) ^ 4)) *
            (Real.log X - 200 * Real.log 2) :=
          mul_le_mul_of_nonneg_right hroute hmargin
        _ ≤ (1 / (5000000000000000 *
            (routeTLogRealShellIndex X t : ℝ) ^ 4)) *
              (Real.log X - 200 * Real.log 2) :=
          mul_le_mul_of_nonneg_right hcoeff hmargin
    have hexp : Real.exp ((1 - σ) * Real.log (((X + 1 : ℕ) : ℝ)) -
        (1 / (5000000000000000 *
          (routeTLogRealShellIndex X t : ℝ) ^ 4)) *
            (Real.log X - 200 * Real.log 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    exact (mul_le_mul_of_nonneg_left hexp (by norm_num)).trans_eq (mul_one 6912)
  · rw [routeTHybridBlockBound, if_neg hlarge]
    let N : ℝ := ((X + 1 : ℕ) : ℝ)
    let η : ℝ := 1 / (3 * (2 : ℝ) ^ (566 : ℕ))
    have hN1 : 1 ≤ N := by
      dsimp only [N]
      exact_mod_cast (by omega : 1 ≤ X + 1)
    have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
    have hmerge : N ^ (1 - σ) * N ^ (-η) = N ^ ((1 - σ) - η) := by
      rw [← Real.rpow_add hN0]
      congr 1
    have hexp : (1 - σ) - η ≤ 0 := by
      dsimp only [η]
      linarith
    have hpow : N ^ ((1 - σ) - η) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 hexp
    change 2560 * N ^ (1 - σ) * N ^ (-η) ≤ 6912
    rw [mul_assoc, hmerge]
    calc
      2560 * N ^ ((1 - σ) - η) ≤ 2560 * 1 :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ 6912 := by norm_num

/-- The complete hybrid estimate on every dyadic block above one certified starting point. -/
theorem norm_routeTZeta_dyadicTail_le_externalHybrid
    {A V R : ℕ} {σ t : ℝ}
    (hA : 1 ≤ A) (hσ : 0 ≤ σ) (ht : 1 < t)
    (hsize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ A)
    (htop : t ≤ (((routeTLogRootBase A ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ))
    (hfac : Nat.factorial 565 ≤ A + 1)
    (hlow : 8 * Real.pi *
      (((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤ t) :
    ‖∑ n ∈ Finset.Ioc A (A * 2 ^ R),
        (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      ∑ r ∈ Finset.range R,
        routeTHybridBlockBound (A * 2 ^ r) σ t := by
  refine (norm_sum_Ioc_dyadic_le A _ R).trans ?_
  apply Finset.sum_le_sum
  intro r hr
  have hrR : r < R := Finset.mem_range.mp hr
  let X := A * 2 ^ r
  have hAX : A ≤ X := by
    dsimp only [X]
    calc
      A = A * 1 := (Nat.mul_one A).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul_left A Nat.one_le_two_pow
  have hX : 1 ≤ X := hA.trans hAX
  have htopX : t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ) := routeT_externalShell_mono hAX htop
  have hsizeX : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ X :=
    hsize.trans hAX
  have hlocalSize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant *
        (routeTLogRealShellIndex X t + 1) ^ 9 + 1)) ≤ X :=
    routeT_degreeNine_size_of_externalShell htopX hsizeX
  have hrTop : r ≤ R - 1 := by omega
  have hpow : 2 ^ r ≤ 2 ^ (R - 1) :=
    Nat.pow_le_pow_right (by norm_num) hrTop
  have hbaseTop : X + 1 ≤ A * 2 ^ (R - 1) + 1 := by
    dsimp only [X]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left A hpow) 1
  have hcastTop : ((X + 1 : ℕ) : ℝ) ≤
      ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hbaseTop
  have hrpowTop : ((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
      ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcastTop (by norm_num)
  have hlowX : 8 * Real.pi * ((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t :=
    (mul_le_mul_of_nonneg_left hrpowTop (by positivity)).trans hlow
  have hfacX : Nat.factorial 565 ≤ X + 1 := hfac.trans (Nat.add_le_add_right hAX 1)
  have hend : A * 2 ^ (r + 1) = 2 * X := by
    dsimp only [X]
    rw [pow_succ]
    ring
  rw [hend]
  change ‖routeTZetaBlockSum X (2 * X) σ t‖ ≤ _
  have hXX : X < 2 * X := by omega
  simpa only [routeTHybridBlockBound, X, Nat.cast_add, Nat.cast_one] using
    norm_routeTZetaBlockSum_le_automaticHybrid
    hX hσ ht hlocalSize hXX le_rfl hfacX hlowX

/-- Inclusive zeta partial sum: trivial head plus the assembled hybrid tail. -/
theorem norm_routeTZeta_partialSum_le_externalHybrid
    {A V R : ℕ} {σ t : ℝ}
    (hA : 2 ≤ A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 1 < t)
    (hsize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ A)
    (htop : t ≤ (((routeTLogRootBase A ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ))
    (hfac : Nat.factorial 565 ≤ A + 1)
    (hlow : 8 * Real.pi *
      (((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤ t) :
    ‖∑ n ∈ Finset.Icc 1 (A * 2 ^ R),
        (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (1 + ((A : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (A : ℝ) ^ (-σ)) +
        ∑ r ∈ Finset.range R, routeTHybridBlockBound (A * 2 ^ r) σ t := by
  let f : ℕ → ℂ := fun n =>
    (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))
  have hAtop : A ≤ A * 2 ^ R := by
    calc
      A = A * 1 := (Nat.mul_one A).symm
      _ ≤ A * 2 ^ R := Nat.mul_le_mul_left A Nat.one_le_two_pow
  have hzeroA : Finset.Ioc 0 A = Finset.Icc 1 A := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hzeroTop : Finset.Ioc 0 (A * 2 ^ R) = Finset.Icc 1 (A * 2 ^ R) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsplit :
      (∑ n ∈ Finset.Icc 1 A, f n) +
        (∑ n ∈ Finset.Ioc A (A * 2 ^ R), f n) =
          ∑ n ∈ Finset.Icc 1 (A * 2 ^ R), f n := by
    rw [← hzeroA, ← hzeroTop]
    exact Finset.sum_Ioc_consecutive f (Nat.zero_le A) hAtop
  have hhead : ‖∑ n ∈ Finset.Icc 1 A, f n‖ ≤
      1 + ((A : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (A : ℝ) ^ (-σ) := by
    simpa only [f, show -((σ : ℂ) + Complex.I * (t : ℂ)) =
      -(σ : ℂ) - Complex.I * (t : ℂ) by ring] using
        norm_dirichlet_sigma_head_le hσ0 hσ1 hA
  have htail : ‖∑ n ∈ Finset.Ioc A (A * 2 ^ R), f n‖ ≤
      ∑ r ∈ Finset.range R, routeTHybridBlockBound (A * 2 ^ r) σ t := by
    exact norm_routeTZeta_dyadicTail_le_externalHybrid (le_trans (by omega) hA)
      hσ0.le ht hsize htop hfac hlow
  rw [← hsplit]
  exact (norm_add_le _ _).trans (add_le_add hhead htail)

/-- In the hybrid strip the inclusive partial sum has only its explicit head plus `6912` per
dyadic block. -/
theorem norm_routeTZeta_partialSum_le_uniform
    {A V R : ℕ} {σ t : ℝ}
    (hA : 2 ≤ A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 1 < t)
    (hsize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ A)
    (htop : t ≤ (((routeTLogRootBase A ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ))
    (hfac : Nat.factorial 565 ≤ A + 1)
    (hlow : 8 * Real.pi *
      (((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤ t)
    (hroute : 2 * (1 - σ) ≤
      1 / (5000000000000000 * (V : ℝ) ^ 4))
    (hderivative : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ (566 : ℕ))) :
    ‖∑ n ∈ Finset.Icc 1 (A * 2 ^ R),
        (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (1 + ((A : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (A : ℝ) ^ (-σ)) +
        (R : ℝ) * 6912 := by
  have hmain := norm_routeTZeta_partialSum_le_externalHybrid hA hσ0 hσ1 ht
    hsize htop hfac hlow
  have hsum : (∑ r ∈ Finset.range R, routeTHybridBlockBound (A * 2 ^ r) σ t) ≤
      (R : ℝ) * 6912 := by
    calc
      (∑ r ∈ Finset.range R, routeTHybridBlockBound (A * 2 ^ r) σ t) ≤
          ∑ _r ∈ Finset.range R, (6912 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _hr
        have hAX : A ≤ A * 2 ^ r := by
          calc
            A = A * 1 := (Nat.mul_one A).symm
            _ ≤ A * 2 ^ r := Nat.mul_le_mul_left A Nat.one_le_two_pow
        have hX : 1 ≤ A * 2 ^ r := (by omega : 1 ≤ A).trans hAX
        have hsizeX : 2 ^ (routeTLogCentreExponent *
            (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ A * 2 ^ r :=
          hsize.trans hAX
        have htopX : t ≤
            (((routeTLogRootBase (A * 2 ^ r) ^ routeTLogCentreExponent) ^
              (4 * V) : ℕ) : ℝ) := routeT_externalShell_mono hAX htop
        exact routeTHybridBlockBound_le hX hσ1.le hsizeX htopX hroute hderivative
      _ = (R : ℝ) * 6912 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine hmain.trans ?_
  linarith

end

end RHTower.Sieve
