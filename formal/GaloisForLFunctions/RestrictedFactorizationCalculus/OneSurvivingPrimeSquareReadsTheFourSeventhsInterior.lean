import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePowerThresholdOfWeightedInteriorPerturbations
import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsBelowTheRoughCofactorCutoff
import GaloisForLFunctions.ArithmeticPositiveDuality.ARationalPrimeBeurlingOneOff

/-!
# The four-sevenths interior at one surviving prime square

Sample the row at X = n p², with p the first prime beyond the wall at n².
Bertrand's theorem makes p subpolynomial, so for large n the prime and
its square survive the actual deletion at X. The quotient is exactly n;
the quotient at the removed head is at most n^(4/7). Constant-weight
Euler inversion at these increasing walls therefore detects the zero
abscissa from this one genuine proper prime power.
-/
noncomputable section
open Finset Filter ArithmeticFunction _root_.RHTower.CoprimeMobius
open scoped Topology Classical
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The first prime strictly above the wall at the squared quotient. -/
def isolatedSquarePrime (n : ℕ) := nextPrime ((logSquareCutoff (n^2):ℝ)+1)

/-- Observation at which this prime square has quotient exactly n. -/
def isolatedSquareObservation (n : ℕ) := n*(isolatedSquarePrime n)^2

private abbrev p := isolatedSquarePrime
private abbrev Xn := isolatedSquareObservation
private abbrev wall (n : ℕ) := logSquareCutoff (Xn n)
private abbrev cut (X : ℕ) := ⌊(X:ℝ)^(4/7:ℝ)⌋₊
private abbrev F (y n : ℕ) := coprimeMoebiusSum (primorial y) n

private theorem prime_spec (n : ℕ) : (p n).Prime ∧ logSquareCutoff (n^2) < p n ∧
    p n ≤ 2*(logSquareCutoff (n^2)+1) := by
  let k := logSquareCutoff (n^2)
  have lo := le_nextPrime ((k:ℝ)+1)
  obtain ⟨P,hP,h₁,h₂⟩ := Nat.exists_prime_lt_and_le_two_mul (k+1) (Nat.succ_ne_zero k)
  have hi : p n ≤ P := nextPrime_le hP (by exact_mod_cast h₁.le)
  exact ⟨nextPrime_prime _,by exact_mod_cast lo,hi.trans h₂⟩

private theorem observation_mono : Monotone Xn := by
  intro i j h
  have hwall := logSquareCutoff_mono (Nat.pow_le_pow_left h 2)
  have hi : p i ≤ p j := nextPrime_mono (add_le_add_right (Nat.cast_le.mpr hwall) 1)
  exact Nat.mul_le_mul h (Nat.pow_le_pow_left hi 2)

private theorem observation_grow : Tendsto Xn atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n (pow_pos (prime_spec n).1.pos 2)) tendsto_id

/-- The selected square grows more slowly than every fixed positive power. -/
theorem selected_prime_square_is_subpolynomial {η : ℝ} (he : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ((p n:ℝ)^2) ≤ (n:ℝ)^η := by
  have ns : Tendsto (fun n : ℕ => n^2) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_self_pow (by decide : 2≠0) n) tendsto_id
  have ge := (tendsto_rpow_atTop (half_pos he)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ns (cutoff_below_power (show 0 < η/8 by positivity)),
    (logSquareCutoff_tendsto_atTop.comp ns).eventually_ge_atTop 1,
    ge.eventually_ge_atTop 4,eventually_ge_atTop 1] with n hw hy hfour hn
  let z := logSquareCutoff (n^2)
  have hpn : (p n:ℝ) ≤ 2*((z:ℝ)+1) := by exact_mod_cast (prime_spec n).2.2
  have hz : (1:ℝ) ≤ z := by exact_mod_cast hy
  have np := (Nat.cast_pos (α:=ℝ)).mpr hn
  change 2*(z:ℝ) ≤ ((n^2:ℕ):ℝ)^(η/8) at hw
  rw [Nat.cast_pow,←Real.rpow_natCast (n:ℝ) 2,←Real.rpow_mul np.le] at hw
  norm_num only [Nat.cast_ofNat] at hw
  have hpower : (p n:ℝ) ≤ 2*((n:ℝ)^(2*(η/8))) := by linarith only [hpn,hz,hw]
  have hp2 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (p n)) hpower 2
  have hh : ((n:ℝ)^(2*(η/8)))^2=(n:ℝ)^(η/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul np.le];congr 1;push_cast;ring
  have h4 : 4 ≤ (n:ℝ)^(η/2) := hfour
  rw [mul_pow,hh] at hp2
  have mul := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg np.le (η/2))
  apply hp2.trans
  norm_num only [Nat.reducePow] at hp2
  calc 4*(n:ℝ)^(η/2) ≤ (n:ℝ)^(η/2)*(n:ℝ)^(η/2) := mul
       _ = _ := by rw [←Real.rpow_add np];congr 1;ring

/-- The selected prime survives the actual log-square wall at its observation. -/
theorem selected_prime_survives_its_observation :
    ∀ᶠ n : ℕ in atTop, Xn n ≤ n^2 ∧ wall n < p n := by
  filter_upwards [selected_prime_square_is_subpolynomial (by norm_num : (0:ℝ) < 1)] with n h
  rw [Real.rpow_one] at h
  have hq : (p n)^2 ≤ n := by exact_mod_cast h
  have hx : Xn n ≤ n^2 := by simpa only [Xn,isolatedSquareObservation,pow_two] using Nat.mul_le_mul_left n hq
  exact ⟨hx,(logSquareCutoff_mono hx).trans_lt (prime_spec n).2.1⟩

private theorem price_at_observation {s η : ℝ} (hs : 1/2 < s) (he : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (deletionPrice s (wall n))^2 ≤ (n:ℝ)^η := by
  filter_upwards [observation_grow (log_square_deletion_cost hs (half_pos he)),
    selected_prime_survives_its_observation,eventually_ge_atTop 1] with n hc hsub hN
  have paid : (deletionPrice s (wall n))^2 ≤ (Xn n:ℝ)^(η/2) :=
    (le_mul_of_one_le_left (sq_nonneg _) (by have := Nat.cast_nonneg (α:=ℝ) (wall n);linarith)).trans hc
  have scale := Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) (Xn n)) (Nat.cast_le.mpr hsub.1) (half_pos he).le
  rw [Nat.cast_pow,←Real.rpow_natCast (n:ℝ) 2,←Real.rpow_mul (Nat.cast_nonneg n)] at scale
  apply paid.trans (scale.trans_eq ?_)
  congr 1;push_cast;ring

private theorem head_at_observation (n : ℕ) :
    ((min (Xn n) (cut (Xn n))/(p n)^2:ℕ):ℝ) ≤ (n:ℝ)^(4/7:ℝ) := by
  let q := (p n)^2
  have qp := pow_pos (prime_spec n).1.pos 2
  have qr := (Nat.cast_pos (α:=ℝ)).mpr qp
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast qp
  have hfloor : ((min (Xn n) (cut (Xn n)):ℕ):ℝ) ≤ (Xn n:ℝ)^(4/7:ℝ) :=
    (Nat.cast_le.mpr (min_le_right ..)).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hsmall := (Nat.cast_le (α:=ℝ)).mpr (Nat.div_mul_le_self (min (Xn n) (cut (Xn n))) q)
  rw [Nat.cast_mul] at hsmall
  have scale : (Xn n:ℝ)^(4/7:ℝ) ≤ (n:ℝ)^(4/7:ℝ)*(q:ℝ) := by
    change ((n*q:ℕ):ℝ)^(4/7:ℝ) ≤ _
    rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) qr.le]
    exact mul_le_mul_of_nonneg_left (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq1 (show (4/7:ℝ) ≤ 1 by norm_num))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact (mul_le_mul_iff_left₀ qr).mp (hsmall.trans (hfloor.trans scale))

/-- The coefficient of the selected proper prime power in the corrected arithmetic reading. -/
def isolatedSquareCoefficient (n : ℕ) :=
  interiorKernel (wall n) (Xn n) (cut (Xn n)) ((p n)^2)

private theorem selected_kernel (n : ℕ) : isolatedSquareCoefficient n=F (wall n) n-
    F (wall n) (min (Xn n) (cut (Xn n))/(p n)^2) := by
  dsimp only [isolatedSquareCoefficient,interiorKernel]
  rw [show Xn n/(p n)^2=n from Nat.mul_div_cancel _ (pow_pos (prime_spec n).1.pos 2)]

private theorem price_one {s η : ℝ} (hs : 1/2 < s) (he : 0 < η) :
    ∀ᶠ n : ℕ in atTop, deletionPrice s (wall n) ≤ (n:ℝ)^η := by
  filter_upwards [price_at_observation hs he] with n hn
  have one := deletionPrice_one_le ((by norm_num : (0:ℝ) < 1/2).trans hs) (wall n)
  exact (show deletionPrice s (wall n) ≤ (deletionPrice s (wall n))^2 by
    nlinarith only [one,sq_nonneg (deletionPrice s (wall n)-1)]).trans hn

private theorem head_paid {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |F (wall n) (min (Xn n) (cut (Xn n))/(p n)^2)| ≤ C*(n:ℝ)^(1/2+ε) := by
  have half : (1/2:ℝ) < 7/8 := by norm_num
  have strip : _root_.RHTower.zetaZeroAbscissa < 7/8 := by
    linarith only [GaloisForLFunctions.ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths]
  obtain ⟨C,hC,rows⟩ := rough_prefix_above_the_zero_abscissa strip
  refine ⟨C,hC,?_⟩
  filter_upwards [price_one half he,eventually_ge_atTop 1] with n hc hn
  have np := (Nat.cast_pos (α:=ℝ)).mpr hn
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) (head_at_observation n) (by norm_num : (0:ℝ) ≤ 7/8)
  rw [←Real.rpow_mul np.le,show (4/7:ℝ)*(7/8)=1/2 by norm_num] at hpow
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hc hC) hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg hC (Real.rpow_nonneg np.le _))
  apply (rows _ _).trans (h.trans_eq ?_)
  rw [mul_assoc,←Real.rpow_add np,add_comm ε]

/-- The exponent of a single surviving proper prime-power coefficient
detects every admissible strip, without access to the ordinary-prime inputs. -/
theorem surviving_square_detects_the_zero_abscissa {β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ,0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |isolatedSquareCoefficient n| ≤ C*(n:ℝ)^(β+ε)) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro hyp
    apply abscissa_from_frozen_rows hb wall (logSquareCutoff_mono.comp observation_mono)
      (fun _ hs _ he => price_at_observation hs he)
    intro η he
    obtain ⟨C,h⟩ := hyp η he
    obtain ⟨D,hD,paid⟩ := head_paid he
    refine ⟨C+D,?_⟩
    filter_upwards [h,paid,eventually_ge_atTop 1] with n hc hh hn
    have hpow := Real.rpow_le_rpow_of_exponent_le ((Nat.one_le_cast (α:=ℝ)).mpr hn) (add_le_add_right hb η)
    have small := hh.trans (mul_le_mul_of_nonneg_left hpow hD)
    let R := F (wall n) (min (Xn n) (cut (Xn n))/(p n)^2)
    have hsum := abs_add_le (isolatedSquareCoefficient n) R
    have eq : isolatedSquareCoefficient n+R=F (wall n) n := by rw [selected_kernel,sub_add_cancel]
    rw [eq] at hsum
    exact hsum.trans ((add_le_add hc small).trans_eq (by ring))
  · intro h ε he
    let u := β+ε/2
    have hu : _root_.RHTower.zetaZeroAbscissa < u := h.trans_lt (lt_add_of_pos_right _ (half_pos he))
    have su := _root_.RHTower.half_le_zetaZeroAbscissa.trans_lt hu
    obtain ⟨C,hC,cap⟩ := rough_prefix_above_the_zero_abscissa hu
    obtain ⟨D,hD,paid⟩ := head_paid he
    refine ⟨C+D,?_⟩
    filter_upwards [price_one su (half_pos he),paid,eventually_ge_atTop 1] with n hprice hh hn
    have np := (Nat.cast_pos (α:=ℝ)).mpr hn
    have hpow := Real.rpow_le_rpow_of_exponent_le ((Nat.one_le_cast (α:=ℝ)).mpr hn) (add_le_add_right hb ε)
    have small := hh.trans (mul_le_mul_of_nonneg_left hpow hD)
    have main : |F (wall n) n| ≤ C*(n:ℝ)^(β+ε) := by
      apply (cap _ _).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprice hC) (Real.rpow_nonneg np.le u)).trans_eq ?_)
      rw [mul_assoc,←Real.rpow_add np,show ε/2+u=β+ε by dsimp only [u];ring]
    rw [selected_kernel]
    exact (abs_sub ..).trans ((add_le_add main small).trans_eq (by ring))

/-- Λ assigns log p to the selected square at the actual observation wall. -/
theorem selected_square_has_its_mangoldt_weight :
    ∀ᶠ n : ℕ in atTop, roughMangoldtWeight (wall n) ((p n)^2)=Real.log (p n) := by
  filter_upwards [selected_prime_survives_its_observation] with n hn
  have hp := (prime_spec n).1
  have free : IsFree (RoughReading.banned (wall n)) (p n) :=
    (isFree_prime _ hp).mpr (show ¬p n ≤ wall n from not_le_of_gt hn.2)
  rw [roughMangoldtWeight,roughRestriction_apply,if_pos (by
    rw [pow_two];exact (isFree_mul_iff _ hp.ne_zero hp.ne_zero).mpr ⟨free,free⟩)]
  simpa only [vonMangoldt_apply_prime hp] using vonMangoldt_apply_pow (n:=p n) (by decide : 2≠0)


/-- Absolute contribution of the actual, surviving proper prime powers. -/
def properInteriorVariation (X : ℕ) :=
  ∑ q∈(Icc 1 X).filter (fun q => ¬q.Prime),roughMangoldtWeight (logSquareCutoff X) q*
    |interiorKernel (logSquareCutoff X) X (cut X) q|

private theorem positive_weight (y q : ℕ) : 0 ≤ roughMangoldtWeight y q := by
  rw [roughMangoldtWeight,roughRestriction_apply]
  split <;> simp [vonMangoldt_nonneg]

/-- Passing from all surviving proper powers to the single selected square
loses no power in the zero-abscissa test. -/
theorem proper_power_variation_detects_the_zero_abscissa {β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ,0 < ε → ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
        properInteriorVariation X ≤ C*(X:ℝ)^(β+ε)) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro prices
    apply (surviving_square_detects_the_zero_abscissa hb).mp
    intro ε he
    let u := β+ε/2
    let γ := (ε/2)/u
    have hu : 0 < u := (by norm_num : (0:ℝ) < 1/2).trans (hb.trans_lt (lt_add_of_pos_right β (half_pos he)))
    have hg : 0 < γ := div_pos (half_pos he) hu
    obtain ⟨C,hC,cap⟩ := prices (ε/2) (half_pos he)
    have hlog := Real.log_pos (by norm_num : (1:ℝ) < 2)
    refine ⟨C/Real.log 2,?_⟩
    filter_upwards [observation_grow cap,selected_square_has_its_mangoldt_weight,
      selected_prime_square_is_subpolynomial hg,eventually_ge_atTop 1] with n hh hweight hsize hn
    let q := (p n)^2
    have hp := (prime_spec n).1
    have qp : 0 < q := pow_pos hp.pos _
    have qle : q ≤ Xn n := by
      change q ≤ n*q
      simpa using Nat.mul_le_mul_right q hn
    have qcomp : ¬q.Prime := fun h => by
      have hh := h.eq_one_or_self_of_dvd (p n) (by change p n ∣ (p n)^2;exact dvd_pow_self _ (by decide))
      rcases hh with h|h
      · exact hp.ne_one h
      · change p n=(p n)^2 at h
        nlinarith only [hp.two_le,h]
    have member : q∈(Icc 1 (Xn n)).filter (fun q => ¬q.Prime) := mem_filter.mpr ⟨mem_Icc.mpr ⟨qp,qle⟩,qcomp⟩
    have sample : roughMangoldtWeight (wall n) q*|isolatedSquareCoefficient n| ≤ properInteriorVariation (Xn n) :=
      single_le_sum (fun i _ => mul_nonneg (positive_weight _ _) (abs_nonneg _)) member
    rw [hweight] at sample
    have logbound := Real.log_le_log (by norm_num : (0:ℝ) < 2) (show (2:ℝ) ≤ p n by exact_mod_cast hp.two_le)
    have ob : (Xn n:ℝ) ≤ (n:ℝ)^(1+γ) := by
      change ((n*(p n)^2:ℕ):ℝ) ≤ _
      rw [Nat.cast_mul,Nat.cast_pow,Real.rpow_add (Nat.cast_pos.mpr hn),Real.rpow_one]
      exact mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _)
    have power := Real.rpow_le_rpow (Nat.cast_nonneg _) ob hu.le
    rw [←Real.rpow_mul (Nat.cast_nonneg _),show (1+γ)*u=β+ε by
      dsimp only [γ];rw [add_mul,one_mul,div_mul_cancel₀ _ hu.ne'];dsimp only [u];ring] at power
    have total := (mul_le_mul_of_nonneg_right logbound (abs_nonneg _)).trans
      (sample.trans (hh.trans (mul_le_mul_of_nonneg_left power hC)))
    calc |isolatedSquareCoefficient n| ≤ C*(n:ℝ)^(β+ε)/Real.log 2 :=
             (le_div_iff₀ hlog).mpr (by simpa only [mul_comm (Real.log 2)] using total)
         _ = _ := by ring
  · intro strip ε he
    let u := min 1 (β+ε/2)
    have su : 1/2 < u := lt_min (by norm_num) (hb.trans_lt (lt_add_of_pos_right β (half_pos he)))
    have du : 0 < u-1/2 := sub_pos.mpr su
    have small : u ≤ 1 := min_le_left ..
    have ub : u ≤ β+ε/2 := min_le_right ..
    obtain ⟨C,hC,hcap⟩ := upper_weighted_sites_all_heads ub
      (strip.trans (le_add_of_nonneg_right (half_pos he).le)) (half_pos he)
    let D := 36/(u-1/2)
    have dp : 0 ≤ D := div_nonneg (by norm_num) du.le
    refine ⟨C*D,mul_nonneg hC dp,hcap.mono fun X cap => ?_⟩
    have hbnd := _root_.RHTower.sum_nonprime_vonMangoldt_rpow_le du
      (by linarith only [small] : u-1/2 ≤ 1) X
    rw [show 1/2+(u-1/2)=u by ring] at hbnd
    have point (q : ℕ) (hq : q∈(Icc 1 X).filter (fun q => ¬q.Prime)) :
        roughMangoldtWeight (logSquareCutoff X) q*|interiorKernel (logSquareCutoff X) X (cut X) q| ≤
          (C*(X:ℝ)^(β+ε))*(vonMangoldt q*(q:ℝ)^(-u)) := by
      have hI := (mem_filter.mp hq).1
      have qr := (Nat.cast_pos (α:=ℝ)).mpr (mem_Icc.mp hI).1
      have hh := cap (cut X) q hI
      rw [show β+ε/2+ε/2=β+ε by ring] at hh
      have price := (le_div_iff₀ (Real.rpow_pos_of_pos qr u)).mpr (by simpa only [mul_comm ((q:ℝ)^u)] using hh)
      have dom := (le_abs_self _).trans (mangoldt_dominated (logSquareCutoff X) q)
      apply (mul_le_mul dom price (abs_nonneg _) vonMangoldt_nonneg).trans_eq
      rw [Real.rpow_neg qr.le];ring
    apply (sum_le_sum point).trans
    rw [←mul_sum]
    exact (mul_le_mul_of_nonneg_left hbnd (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq (by dsimp only [D];ring)

end GaloisForLFunctions.RestrictedFactorizationCalculus
