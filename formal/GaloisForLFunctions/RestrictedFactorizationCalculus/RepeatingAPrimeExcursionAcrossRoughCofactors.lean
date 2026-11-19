import GaloisForLFunctions.RestrictedFactorizationCalculus.IndependentPrimeWindowsOnRoughCofactors
import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsInTheCenteredUnitWindow
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary

/-!
# A shared prime excursion across polynomially many quotient windows

Every prime cofactor above the sieve has negative sign. The very same
prime-error excursion can occur in all its allowed quotient subwindows.
Independent choices of signed proper powers cannot remove either sign.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem sign_of_a_prime_cofactor {y p : ℕ} (hp : p.Prime) (above : y<p) : RoughReading.row y p= -1 := by
  have good := (isFree_prime (RoughReading.banned y) hp).mpr (not_le.mpr above)
  rw [RoughReading.row_value,if_pos good,moebius_apply_prime hp]
  norm_num

/-- The common ordinary window (y,T] contributes its error once for
every chosen prime cofactor. The floor at the prime wall is exact. -/
theorem one_prime_interval_at_every_selected_prime_cofactor {y T : ℕ} (order : y ≤ T) (S : Finset ℕ)
    (prime : ∀ m ∈ S,m.Prime ∧ y< m) :
    (∑ m ∈ S,RoughReading.row y m*centeredPrimeInterval (roughOrdinaryPrimeWeight y) y y T)=
      -(S.card:ℝ)*(ordinaryThetaError T-ordinaryThetaError y+((T%y:ℕ):ℝ)) := by
  simp only [centered_ordinary_prime_interval le_rfl order,Nat.mod_self,Nat.cast_zero,sub_zero]
  rw [sum_congr rfl (fun m hm => congrArg (fun z : ℝ => z*_) (sign_of_a_prime_cofactor (prime m hm).1 (prime m hm).2))]
  rw [sum_const,nsmul_eq_mul]
  ring

/-- Uniformly up to the square root in the sieve, all edited prime
windows differ from the genuine top prime error by only O(√T). -/
private theorem cost_at_the_lower_sieve_endpoint :
    ∃ D : ℝ,0 ≤ D ∧ ∀ y T : ℕ,1 ≤ y → y ≤ T → (y:ℝ) ≤ Real.sqrt T →
      ∀ a : ArithmeticFunction ℝ,(∀ q ∈ Ioc y T,|a q| ≤ vonMangoldt q) →
      (∀ q ∈ Ioc y T,q.Prime → a q=roughOrdinaryPrimeWeight y q) →
      |centeredPrimeInterval a y y T-ordinaryThetaError T| ≤ D*Real.sqrt T := by
  obtain ⟨C,primePower⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have lc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨max 0 C+Real.log 4+2,by positivity,fun y T yp yT small a dom fix => ?_⟩
  have extra := (proper_power_edits_in_a_prime_interval a dom fix).trans ((primePower T).trans
    (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Real.sqrt_nonneg _)))
  have prime := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) y)
  have per : |ordinaryThetaError y| ≤ (Real.log 4+1)*(y:ℝ) := by
    change |Chebyshev.theta y-y| ≤ _
    have tri := abs_sub (Chebyshev.theta y) (y:ℝ)
    rw [abs_of_nonneg (Chebyshev.theta_nonneg (y:ℝ)),abs_of_nonneg (Nat.cast_nonneg (α := ℝ) y)] at tri
    linarith only [tri,prime]
  have residue : ((T%y:ℕ):ℝ) ≤ y := Nat.cast_le.mpr (Nat.mod_lt _ yp).le
  let b := roughOrdinaryPrimeWeight y
  have lower : |centeredPrimeInterval b y y T-ordinaryThetaError T| ≤ (Real.log 4+2)*y := by
    rw [centered_ordinary_prime_interval le_rfl yT,Nat.mod_self,Nat.cast_zero,sub_zero,
      show ordinaryThetaError T-ordinaryThetaError y+((T%y:ℕ):ℝ)-ordinaryThetaError T=((T%y:ℕ):ℝ)-ordinaryThetaError y by ring]
    apply (abs_sub ..).trans
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    linarith only [residue,per]
  have big := lower.trans (mul_le_mul_of_nonneg_left small (by linarith only [lc]))
  have tri := abs_sub_le (centeredPrimeInterval a y y T) (centeredPrimeInterval b y y T) (ordinaryThetaError T)
  change |centeredPrimeInterval a y y T-centeredPrimeInterval b y y T| ≤ _ at extra
  linarith only [tri,big,extra]

/-- For either sign, one sequence of observations works for all sieve
walls up to √T and for every family of signed proper-power selections.
All chosen prime cofactors can use the common physical interval (y,T]. -/
theorem simultaneous_excursions_repeated_at_prime_cofactors :
    ∃ δ : ℝ,0<δ ∧ ∀ σ : ℝ,σ=1 ∨ σ= -1 →
      ∃ᶠ T : ℕ in atTop,∀ y : ℕ,1 ≤ y → y ≤ T → (y:ℝ) ≤ Real.sqrt T →
        ∀ S : Finset ℕ,(∀ m ∈ S,m.Prime ∧ y< m) → ∀ a : ℕ → ArithmeticFunction ℝ,
        (∀ m ∈ S,∀ q ∈ Ioc y T,|a m q| ≤ vonMangoldt q) →
        (∀ m ∈ S,∀ q ∈ Ioc y T,q.Prime → a m q=roughOrdinaryPrimeWeight y q) →
        (S.card:ℝ)*(δ*Real.sqrt T*Real.log (Real.log (Real.log T))) ≤
          -σ*∑ m ∈ S,RoughReading.row y m*centeredPrimeInterval (a m) y y T := by
  obtain ⟨D,d0,cost⟩ := cost_at_the_lower_sieve_endpoint
  let c := RHTower.littlewoodConst/28
  have cp : 0<c := div_pos RHTower.littlewoodConst_pos (by norm_num)
  refine ⟨c/4,div_pos cp (by norm_num),fun σ dir => frequently_atTop.mpr (fun N => ?_)⟩
  obtain ⟨t,size,record,large,_⟩ := oriented_prime_error_records σ dir (2*D) (max N 1)
  have tp := (le_max_right N 1).trans size
  have root := Real.sqrt_pos.mpr (Nat.cast_pos.mpr tp)
  have pay := (lt_div_iff₀ root).mp record
  have gain := (lt_div_iff₀ root).mp large
  refine ⟨t,(le_max_left N 1).trans size,fun y yp yt small S prime a dom fix => ?_⟩
  have per (m : ℕ) (hm : m ∈ S) : c/4*Real.sqrt t*Real.log (Real.log (Real.log t)) ≤
      -σ*(RoughReading.row y m*centeredPrimeInterval (a m) y y t) := by
    rw [sign_of_a_prime_cofactor (prime m hm).1 (prime m hm).2,neg_one_mul,neg_mul_neg]
    have bound := cost y t yp yt small (a m) (dom m hm) (fix m hm)
    have oriented : |σ*(centeredPrimeInterval (a m) y y t-ordinaryThetaError t)| ≤ D*Real.sqrt t := by
      rcases dir with h | h <;> simpa only [h,one_mul,neg_one_mul,abs_neg] using bound
    change c/2*Real.log (Real.log (Real.log t))*Real.sqrt t < σ*ordinaryThetaError t at gain
    linarith only [(abs_le.mp oriented).1,pay,gain]
  simpa only [sum_const,nsmul_eq_mul,←mul_sum] using sum_le_sum per

/-- The observation enclosing a prime octave of scale T^a and a common
prime window ending at T. The ceiling retains every prime in the octave. -/
def primeRectangleHeight (a : ℝ) (T : ℕ) := T*⌈2*(T:ℝ)^a⌉₊

private theorem rectangle_size {a : ℝ} (ap : 0<a) {T : ℕ} (tp : 1 ≤ T) :
    T ≤ primeRectangleHeight a T ∧ (primeRectangleHeight a T:ℝ) ≤ 3*(T:ℝ)^(1+a) := by
  have t1 : (1:ℝ) ≤ T := Nat.one_le_cast.mpr tp
  have v1 := Real.one_le_rpow t1 ap.le
  have v0 := Real.rpow_nonneg (Nat.cast_nonneg T) a
  have hi := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) v0)
  have lo := Nat.le_ceil (2*(T:ℝ)^a)
  have z1 : 1 ≤ ⌈2*(T:ℝ)^a⌉₊ := Nat.one_le_cast.mp (by linarith only [v1,lo] : (1:ℝ) ≤ (⌈2*(T:ℝ)^a⌉₊:ℕ))
  refine ⟨by simpa only [primeRectangleHeight,Nat.mul_one] using Nat.mul_le_mul_left T z1,?_⟩
  rw [primeRectangleHeight,Nat.cast_mul,Real.rpow_add (zero_lt_one.trans_le t1),Real.rpow_one]
  have cap := mul_le_mul_of_nonneg_left (by linarith only [hi,v1] : (⌈2*(T:ℝ)^a⌉₊:ℝ) ≤ 3*(T:ℝ)^a) (Nat.cast_nonneg (α := ℝ) T)
  linarith only [cap]

private theorem log_square_wall_inside_a_prime_rectangle {a : ℝ} (ap : 0<a) :
    ∀ᶠ T : ℕ in atTop, let y := logSquareCutoff (primeRectangleHeight a T)
      1 ≤ y ∧ (y:ℝ)<(T:ℝ)^a ∧ (y:ℝ) ≤ Real.sqrt T ∧ y ≤ T := by
  have growth : Tendsto (primeRectangleHeight a) atTop atTop := tendsto_atTop_mono
    (fun T => (Nat.eq_zero_or_pos T).elim (by rintro rfl; exact Nat.zero_le _) (fun h => (rectangle_size ap h).1)) tendsto_id
  let d := min a (1/2:ℝ)
  let h := d/(2+a)
  have dp : 0<d := lt_min ap (by norm_num)
  have den : 0<2+a := by linarith only [ap]
  have hp : 0<h := div_pos dp den
  have wall := growth.eventually (log_square_deletion_cost (by norm_num : (1:ℝ)/2<1) hp)
  filter_upwards [wall,(logSquareCutoff_tendsto_atTop.comp growth).eventually_ge_atTop 1,
    eventually_ge_atTop (3:ℕ)] with T cheap alive T3
  let X := primeRectangleHeight a T
  let y := logSquareCutoff X
  have t3 : (3:ℝ) ≤ T := by exact_mod_cast T3
  have t1 : (1:ℝ) ≤ T := by linarith only [t3]
  have t0 := zero_lt_one.trans_le t1
  have width : (X:ℝ) ≤ (T:ℝ)^(2+a) := by
    have room := (rectangle_size ap (by omega : 1 ≤ T)).2.trans (mul_le_mul_of_nonneg_right t3
      (Real.rpow_nonneg (Nat.cast_nonneg T) (1+a)))
    rwa [show (2:ℝ)+a=1+(1+a) by ring,Real.rpow_add t0,Real.rpow_one]
  have es := one_le_pow₀ (deletionPrice_one_le (by norm_num : (0:ℝ)<1) y) (n := 2)
  have cost : (y:ℝ)+1 ≤ (X:ℝ)^h :=
    (le_mul_of_one_le_right (by positivity : 0 ≤ (y:ℝ)+1) es).trans cheap
  have power := Real.rpow_le_rpow (Nat.cast_nonneg X) width hp.le
  rw [←Real.rpow_mul t0.le,show (2+a)*h=d by dsimp only [h]; field_simp [den.ne']] at power
  have less : (y:ℝ)<(T:ℝ)^d := by linarith only [cost,power]
  have root := less.le.trans (Real.rpow_le_rpow_of_exponent_le t1 (min_le_right a (1/2:ℝ)))
  rw [←Real.sqrt_eq_rpow] at root
  exact ⟨alive,less.trans_le (Real.rpow_le_rpow_of_exponent_le t1 (min_le_left a (1/2:ℝ))),root,
    Nat.cast_le.mp (root.trans (Real.sqrt_le_self_iff.mpr (Or.inr t1)))⟩

/-- Every exponent below (a+1/2)/(a+1) fails, in both orientations,
even for the common window (y,T] at prime cofactors in one octave.
All the windows lie within their individual physical quotient ranges. -/
theorem both_signs_above_every_smaller_rectangle_power {a r : ℝ} (ap : 0<a) (rp : 0 ≤ r)
    (short : (1+a)*r<a+1/2) (B : ℝ) (σ : ℝ) (dir : σ=1 ∨ σ= -1) :
    ∃ᶠ T : ℕ in atTop, let X := primeRectangleHeight a T
      let y := logSquareCutoff X
      let S := RHTower.windowPrimes ((T:ℝ)^a) (2*(T:ℝ)^a)
      (∀ m ∈ S,y< m ∧ T ≤ X/m) ∧ ∀ w : ℕ → ArithmeticFunction ℝ,
        (∀ m ∈ S,∀ q ∈ Ioc y T,|w m q| ≤ vonMangoldt q) →
        (∀ m ∈ S,∀ q ∈ Ioc y T,q.Prime → w m q=roughOrdinaryPrimeWeight y q) →
        B*(X:ℝ)^r < -σ*∑ m ∈ S,RoughReading.row y m*centeredPrimeInterval (w m) y y T := by
  obtain ⟨δ,δp,excursion⟩ := simultaneous_excursions_repeated_at_prime_cofactors
  let k := (a+1/2-(1+a)*r)/2
  let A := max 1 B*(3:ℝ)^r
  let D := Real.log 2+a/k
  have kp : 0<k := div_pos (sub_pos.mpr short) (by norm_num)
  have Apos : 0<A := mul_pos (zero_lt_one.trans_le (le_max_left ..)) (Real.rpow_pos_of_pos (by norm_num) _)
  have denom : 0<(99/100:ℝ)*δ := mul_pos (by norm_num) δp
  have casts := tendsto_natCast_atTop_atTop (R := ℝ)
  have power (p : ℝ) (pp : 0<p) : Tendsto (fun T : ℕ => (T:ℝ)^p) atTop atTop :=
    (tendsto_rpow_atTop pp).comp casts
  have late := (log_square_wall_inside_a_prime_rectangle ap).and ((power a ap).eventually eventually_dyadic_prime_lower)
  have logs := (RHTower.tendsto_logLogLog_atTop.comp casts).eventually_ge_atTop 1
  apply ((excursion σ dir).and_eventually (late.and (logs.and
    (((power k kp).eventually_gt_atTop (A*D/((99/100:ℝ)*δ))).and (eventually_ge_atTop (1:ℕ)))))).mono
  rintro T ⟨large,⟨⟨wall,count⟩,ltop,scale,tp⟩⟩
  let X := primeRectangleHeight a T
  let y := logSquareCutoff X
  let v := (T:ℝ)^a
  let S := RHTower.windowPrimes v (2*v)
  have t1 : (1:ℝ) ≤ T := Nat.one_le_cast.mpr tp
  have t0 := zero_lt_one.trans_le t1
  have v1 : 1 ≤ v := Real.one_le_rpow t1 ap.le
  have v0 := zero_lt_one.trans_le v1
  have primes (m : ℕ) (hm : m ∈ S) := (RHTower.mem_windowPrimes v0.le (mul_nonneg (by norm_num) v0.le)).mp hm
  have prime (m : ℕ) (hm : m ∈ S) : m.Prime ∧ y< m :=
    ⟨(primes m hm).1,Nat.cast_lt.mp (wall.2.1.trans (primes m hm).2.1)⟩
  refine ⟨fun m hm => ⟨(prime m hm).2,(Nat.le_div_iff_mul_le (prime m hm).1.pos).mpr
    (Nat.mul_le_mul_left T (Nat.cast_le.mp ((primes m hm).2.2.trans (Nat.le_ceil _))))⟩,?_⟩
  intro w dom fixed
  have result := large y wall.1 wall.2.2.2 wall.2.2.1 S prime w dom fixed
  have cost : B*(X:ℝ)^r ≤ A*(T:ℝ)^((1+a)*r) := by
    have ht := Real.rpow_le_rpow (Nat.cast_nonneg X) (rectangle_size ap tp).2 rp
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg t0.le _),←Real.rpow_mul t0.le] at ht
    exact (mul_le_mul (le_max_right 1 B) ht (Real.rpow_nonneg (Nat.cast_nonneg X) _) (le_of_lt (zero_lt_one.trans_le (le_max_left ..)))).trans_eq (by dsimp only [A]; ring)
  have lpos : 0<Real.log (2*v) := Real.log_pos (by linarith only [v1])
  have l2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have lcap : Real.log (2*v) ≤ D*(T:ℝ)^k := by
    rw [Real.log_mul (by norm_num) v0.ne',show Real.log v=a*Real.log T from Real.log_rpow t0 a]
    have h1 := mul_le_mul_of_nonneg_left (Real.one_le_rpow t1 kp.le) l2
    have h2 := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div t0.le kp) ap.le
    dsimp only [D]
    simp only [div_eq_mul_inv] at h2 ⊢
    linarith only [h1,h2]
  have exponent : (1+a)*r+k+k=a+1/2 := by dsimp only [k]; ring
  have scaled := mul_lt_mul_of_pos_right ((div_lt_iff₀ denom).mp scale)
    (Real.rpow_pos_of_pos t0 ((1+a)*r+k))
  have room : A*(T:ℝ)^((1+a)*r)*Real.log (2*v) < (99/100)*v*(δ*Real.sqrt T) := by
    apply (mul_le_mul_of_nonneg_left lcap (mul_nonneg Apos.le (Real.rpow_nonneg t0.le _))).trans_lt
    have eqp : (T:ℝ)^((1+a)*r)*(T:ℝ)^k*(T:ℝ)^k=v*Real.sqrt T := by
      rw [←Real.rpow_add t0,←Real.rpow_add t0,exponent,Real.rpow_add t0,←Real.sqrt_eq_rpow]
    rw [Real.rpow_add t0] at scaled
    nlinarith only [scaled,congrArg (fun z : ℝ => (99/100)*δ*z) eqp]
  have root : 0 ≤ δ*Real.sqrt T := mul_nonneg δp.le (Real.sqrt_nonneg _)
  have cheap : A*(T:ℝ)^((1+a)*r)<((99/100)*v/Real.log (2*v))*(δ*Real.sqrt T) :=
    (lt_div_iff₀ lpos).mpr room |>.trans_eq (by ring)
  have cnt := mul_le_mul_of_nonneg_right count root
  have last := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right root ltop) (Nat.cast_nonneg (α := ℝ) S.card)
  exact cost.trans_lt (cheap.trans_le (cnt.trans (last.trans result)))

private abbrev rectanglePrimes (a : ℝ) (T : ℕ) :=
  RHTower.windowPrimes ((T:ℝ)^a) (2*(T:ℝ)^a)

/-- The same sharp prime interval at every prime cofactor in one octave.
The weights at proper prime powers may depend on the cofactor. -/
def primeRectangleReading (a : ℝ) (w : ℕ → ArithmeticFunction ℝ) (T : ℕ) :=
  let y := logSquareCutoff (primeRectangleHeight a T)
  ∑ m ∈ rectanglePrimes a T,RoughReading.row y m*centeredPrimeInterval (w m) y y T

/-- The prime multiplicity of the octave is T^a up to every small power. -/
private theorem rectangle_multiplicity {a η : ℝ} (ap : 0<a) (ep : 0<η) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ T : ℕ in atTop,
      (T:ℝ)^a ≤ D*(T:ℝ)^η*(rectanglePrimes a T).card ∧
      ((rectanglePrimes a T).card:ℝ) ≤ 2*(T:ℝ)^a := by
  let D := (100/99:ℝ)*(Real.log 2+a/η)
  have l2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have dp : 0<D := mul_pos (by norm_num) (add_pos l2 (div_pos ap ep))
  have power : Tendsto (fun T : ℕ => (T:ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ap).comp tendsto_natCast_atTop_atTop
  refine ⟨D,dp,?_⟩
  filter_upwards [power.eventually eventually_dyadic_prime_lower,eventually_ge_atTop (1:ℕ)] with T count one
  let S := rectanglePrimes a T
  let v := (T:ℝ)^a
  have t1 : (1:ℝ) ≤ T := Nat.one_le_cast.mpr one
  have t0 := zero_lt_one.trans_le t1
  have v1 : 1 ≤ v := Real.one_le_rpow t1 ap.le
  have v0 := zero_lt_one.trans_le v1
  have lpos : 0<Real.log (2*v) := Real.log_pos (by linarith only [v1])
  have upper : S.card ≤ ⌊2*v⌋₊ := by
    apply (card_filter_le ..).trans
    rw [Nat.card_Ioc]
    exact Nat.sub_le _ _
  refine ⟨?_,(Nat.cast_le.mpr upper).trans (Nat.floor_le (by positivity))⟩
  have lcap : Real.log (2*v) ≤ (Real.log 2+a/η)*(T:ℝ)^η := by
    rw [Real.log_mul (by norm_num) v0.ne',show Real.log v=a*Real.log T from Real.log_rpow t0 a]
    have h1 := mul_le_mul_of_nonneg_left (Real.one_le_rpow t1 ep.le) l2.le
    have h2 := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div t0.le ep) ap.le
    simp only [div_eq_mul_inv] at h2 ⊢
    linarith only [h1,h2]
  have bound := ((div_le_iff₀ lpos).mp count).trans
    (mul_le_mul_of_nonneg_left lcap (Nat.cast_nonneg (α := ℝ) S.card))
  change v ≤ D*(T:ℝ)^η*S.card
  dsimp only [D]
  linarith only [bound]

private theorem compare_rectangle_with_prime_error {a : ℝ} (ap : 0<a) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ᶠ T : ℕ in atTop, let y := logSquareCutoff (primeRectangleHeight a T)
      ∀ w : ℕ → ArithmeticFunction ℝ,
      (∀ m ∈ rectanglePrimes a T,∀ q ∈ Ioc y T,|w m q| ≤ vonMangoldt q) →
      (∀ m ∈ rectanglePrimes a T,∀ q ∈ Ioc y T,q.Prime → w m q=roughOrdinaryPrimeWeight y q) →
      let n : ℝ := (rectanglePrimes a T).card
      |primeRectangleReading a w T| ≤ n*(|ordinaryThetaError T|+D*Real.sqrt T) ∧
      n*|ordinaryThetaError T| ≤ |primeRectangleReading a w T|+n*(D*Real.sqrt T) := by
  obtain ⟨D,d0,bound⟩ := cost_at_the_lower_sieve_endpoint
  refine ⟨D,d0,?_⟩
  filter_upwards [log_square_wall_inside_a_prime_rectangle ap,eventually_ge_atTop (1:ℕ)] with T room tp
  intro y w dom prime
  let S := rectanglePrimes a T
  let v := (T:ℝ)^a
  let E := ordinaryThetaError T
  let R := primeRectangleReading a w T
  let e := fun m => RoughReading.row y m*centeredPrimeInterval (w m) y y T
  have v0 : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg T) _
  have step (m : ℕ) (hm : m ∈ S) : |e m+E| ≤ D*Real.sqrt T := by
    obtain ⟨p,lo,_⟩ := (RHTower.mem_windowPrimes v0 (mul_nonneg (by norm_num) v0)).mp hm
    have above : y< m := Nat.cast_lt.mp (room.2.1.trans lo)
    change |RoughReading.row y m*centeredPrimeInterval (w m) y y T+E| ≤ _
    rw [sign_of_a_prime_cofactor p above,neg_one_mul,neg_add_eq_sub,abs_sub_comm]
    exact bound y T room.1 room.2.2.2 room.2.2.1 _ (dom m hm) (prime m hm)
  have diff := (abs_sum_le_sum_abs (fun m => e m+E) S).trans (sum_le_sum step)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at diff
  change |R+(S.card:ℝ)*E| ≤ (S.card:ℝ)*(D*Real.sqrt T) at diff
  have left := abs_sub (R+(S.card:ℝ)*E) ((S.card:ℝ)*E)
  have right := abs_sub (R+(S.card:ℝ)*E) R
  have factor : |(S.card:ℝ)*E| = (S.card:ℝ)*|E| := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) S.card)]
  rw [add_sub_cancel_right,factor] at left
  rw [add_sub_cancel_left,factor] at right
  change |R| ≤ _ ∧ (S.card:ℝ)*|E| ≤ _
  constructor <;> linarith only [left,right,diff]

private theorem theta_spectrum_at {β : ℝ} (critical : 1/2 ≤ β) :
    (∀ ε : ℝ,0<ε → PrefixPower (β+ε) ordinaryThetaError) ↔ RHTower.zetaZeroAbscissa ≤ β := by
  have nonneg := sub_nonneg.mpr critical
  have width := zero_width_of_the_centered_unit_window nonneg
    (fun X => roughOrdinaryPrimeWeight (logSquareCutoff X)) (fun X => ordinary_dominated _) (fun _ _ _ => rfl)
  rw [RHTower.xiZeroHalfPlaneBound_iff_zetaZeroAbscissa_le nonneg,show (1:ℝ)/2+(β-1/2)=β by ring] at width
  rw [←width]
  apply forall_congr'
  intro ε
  apply imp_congr_right
  intro ep
  exact (centered_unit_window_power_iff_prime_error
    (by linarith only [critical,ep] : 0<β+ε)).symm

/-- At the genuine observation X = T ceil(2T^a), one sharp prime rectangle
has exponent a+Θ in the T coordinate. The classification applies to
every separate choice of the proper-power weights in every row and at
every observation. -/
theorem sharp_exponent_of_a_single_prime_rectangle {a β : ℝ} (ap : 0<a) (critical : 1/2 ≤ β)
    (w : ℕ → ℕ → ArithmeticFunction ℝ)
    (dom : ∀ T m q,|w T m q| ≤ vonMangoldt q)
    (fix : ∀ T m p,p.Prime → w T m p=roughOrdinaryPrimeWeight (logSquareCutoff (primeRectangleHeight a T)) p) :
    (∀ ε : ℝ,0<ε → PrefixPower (a+β+ε) (fun T => primeRectangleReading a (w T) T)) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  obtain ⟨D,d0,approx⟩ := compare_rectangle_with_prime_error ap
  rw [←theta_spectrum_at critical]
  constructor
  · intro rectangles ε ep
    let η := ε/2
    have hp : 0<η := half_pos ep
    obtain ⟨C,c0,paid⟩ := rectangles η hp
    obtain ⟨A,apos,count⟩ := rectangle_multiplicity ap hp
    apply prefixPower_of_eventual (C := A*C+D) (by simp [ordinaryThetaError,Chebyshev.theta]) (by linarith only [critical,ep])
    filter_upwards [count,approx,eventually_ge_atTop (1:ℕ)] with T ncap cost tp
    let n : ℝ := (rectanglePrimes a T).card
    let t := (T:ℝ)
    let R := primeRectangleReading a (w T) T
    let E := ordinaryThetaError T
    have t1 : 1 ≤ t := Nat.one_le_cast.mpr tp
    have t0 := zero_lt_one.trans_le t1
    have mult := ncap.1
    change t^a ≤ A*t^η*n at mult
    have once := (cost (w T) (fun m _ q _ => dom T m q) (fun m _ p _ => fix T m p)).2
    change n*|E| ≤ |R|+n*(D*Real.sqrt t) at once
    have known := paid T
    change |R| ≤ C*t^(a+β+η) at known
    have price : |R| ≤ n*(A*C*t^(β+ε)) := by
      rw [show a+β+η=a+(β+η) by ring,Real.rpow_add t0] at known
      have h := mul_le_mul_of_nonneg_right mult (mul_nonneg c0 (Real.rpow_nonneg t0.le (β+η)))
      have ex : t^η*t^(β+η)=t^(β+ε) := by rw [←Real.rpow_add t0]; congr 1; dsimp only [η]; ring
      calc |R| ≤ C*(t^a*t^(β+η)) := known
           _ ≤ (A*t^η*n)*(C*t^(β+η)) := by linarith only [h]
           _ = n*(A*C*t^(β+ε)) := by rw [←ex]; ring
    have np : 0<n := by
      by_contra! low
      have p := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg apos.le (Real.rpow_nonneg t0.le η)) low
      exact (not_le_of_gt (Real.rpow_pos_of_pos t0 a)) (mult.trans p)
    have roots : Real.sqrt t ≤ t^(β+ε) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le t1 (by linarith only [critical,ep])
    have last := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left roots d0) np.le
    apply le_of_mul_le_mul_left _ np
    change n*|E| ≤ n*((A*C+D)*t^(β+ε))
    linarith only [price,once,last]
  · intro all ε ep
    obtain ⟨C,c0,prime⟩ := all ε ep
    obtain ⟨_,_,count⟩ := rectangle_multiplicity ap ep
    have bp : 0<a+β+ε := by linarith only [ap,critical,ep]
    apply prefixPower_of_eventual (C := 2*(C+D)) (by
      simp [primeRectangleReading,centeredPrimeInterval,Finset.Ioc_eq_empty_of_le]) bp
    filter_upwards [count,approx,eventually_ge_atTop (1:ℕ)] with T ncap cost tp
    let t := (T:ℝ)
    have t1 : 1 ≤ t := Nat.one_le_cast.mpr tp
    have t0 := zero_lt_one.trans_le t1
    have sq : Real.sqrt T ≤ t^(β+ε) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le t1 (by linarith only [critical,ep])
    have bound := (cost (w T) (fun m _ q _ => dom T m q) (fun m _ p _ => fix T m p)).1
    have localPrice :=  add_le_add (prime T) (mul_le_mul_of_nonneg_left sq d0)
    have pay := mul_le_mul ncap.2 localPrice (add_nonneg (abs_nonneg _) (mul_nonneg d0 (Real.sqrt_nonneg _)))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg t0.le _))
    apply bound.trans (pay.trans_eq ?_)
    change 2*t^a*(C*t^(β+ε)+D*t^(β+ε)) = 2*(C+D)*t^(a+β+ε)
    rw [show a+β+ε=a+(β+ε) by ring,Real.rpow_add t0 a (β+ε)]
    ring

#print axioms sharp_exponent_of_a_single_prime_rectangle

#print axioms both_signs_above_every_smaller_rectangle_power

#print axioms one_prime_interval_at_every_selected_prime_cofactor
#print axioms simultaneous_excursions_repeated_at_prime_cofactors
end GaloisForLFunctions.RestrictedFactorizationCalculus
