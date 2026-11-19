import Mathlib.Analysis.MeanInequalitiesPow
import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola
import GaloisForLFunctions.RestrictedFactorizationCalculus.TotalVariationOfTheRemovedQuotientHead
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity

/-!
# Prime arrivals in the variation of signed quotient heads

Each ordinary prime above the final wall enters the increasing head
once. A simultaneous sieve jump can erase at most one such observation.
At unchanged walls changing proper powers costs only their signed action
on the smaller common head.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev headAt (a : ArithmeticFunction ℝ) (y t : ℕ) :=
  quotientReading (roughFloorCoefficient y a) t

private theorem coefficient_at_an_arriving_prime (y : ℕ) (a : ArithmeticFunction ℝ)
    (unit : a 1=0) {p : ℕ} (pr : p.Prime) :
    roughFloorCoefficient y a p=a p := by
  rw [roughFloorCoefficient,ArithmeticFunction.mul_apply]
  have unitMu : roughMobiusWeight y 1=1 := by
    simp [roughMobiusWeight,roughRestriction_apply,isFree_one]
  rw [sum_eq_single (1,p)]
  · simp [unitMu]
  · rintro ⟨d,q⟩ h diff
    obtain ⟨fac,_⟩ := Nat.mem_divisorsAntidiagonal.mp h
    change d*q=p at fac
    have dvd : q ∣ p := fac ▸ dvd_mul_left q d
    rcases (Nat.dvd_prime pr).mp dvd with one | pval
    · simp [one,unit]
    · subst q
      have d1 : d=1 := Nat.eq_of_mul_eq_mul_right pr.pos (by simpa only [one_mul] using fac : d*p=1*p)
      exact (diff (by simp [d1])).elim
  · intro bad
    exact (bad (Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.one_mul _,pr.ne_zero⟩)).elim

private theorem add_one_coefficient (a : ArithmeticFunction ℝ) (y i : ℕ) :
    headAt a y (i+1)=headAt a y i+roughFloorCoefficient y a (i+1) := by
  unfold headAt quotientReading
  rw [sum_Icc_succ_top (Nat.succ_pos _)]

private def nextAtSameWall (Y : ℕ → ℕ) (a : ℕ → ArithmeticFunction ℝ) (i : ℕ) :=
  if Y (i+1)=Y i then a (i+1) else a i

private theorem common_edits_on_unchanged_walls {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s)
    (upper : s ≤ 1) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ N : ℕ,∀ Y H : ℕ → ℕ,Monotone Y → Monotone H →
      ∀ a : ℕ → ArithmeticFunction ℝ,(∀ i p,p.Prime → a i p=roughOrdinaryPrimeWeight (Y i) p) →
      ∀ B : ℝ,0 ≤ B → (∀ q,¬q.Prime → (∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) →
      (∑ i ∈ range N,|headAt (nextAtSameWall Y a i) (Y i) (H i)-headAt (a i) (Y i) (H i)|) ≤
        K*B*deletionPrice s (Y N)*(H N:ℝ)^s := by
  obtain ⟨K,k0,cap⟩ := signed_price_of_all_proper_power_edits strip upper
  refine ⟨K,k0,fun N Y H mono heights a ordinary B bp variation => ?_⟩
  let b := nextAtSameWall Y a
  have fixed (i p : ℕ) (_ : i<N) (hp : p.Prime) : b i p=a i p := by
    dsimp only [b,nextAtSameWall]
    split
    · rename_i eq
      rw [ordinary _ _ hp,ordinary _ _ hp,eq]
    · rfl
  have changes (q : ℕ) : (∑ i ∈ range N,|b i q-a i q|) ≤ B*vonMangoldt q := by
    by_cases pr : q.Prime
    · apply le_trans _ (mul_nonneg bp vonMangoldt_nonneg)
      exact (sum_eq_zero (fun i hi => by rw [fixed i q (mem_range.mp hi) pr,sub_self,abs_zero])).le
    · apply le_trans _ (variation q pr)
      apply sum_le_sum
      intro i _
      dsimp only [b,nextAtSameWall]
      split
      · exact le_rfl
      · rw [sub_self,abs_zero]; exact abs_nonneg _
  exact cap N (Y N) (H N) Y H (fun _ h => mono h.le) (fun _ h => heights h.le) a b B bp fixed changes

/-- The prime mass beyond the last sieve is paid either by path
variation, by a simultaneous sieve jump, or by a genuine weight edit.
The signed price of all proper-power edits uses only a weaker strip. -/
theorem prime_arrivals_force_head_variation {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s)
    (upper : s ≤ 1) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ N : ℕ,∀ Y H : ℕ → ℕ,Monotone Y → Monotone H →
      (∀ i,i<N → H (i+1) ≤ H i+1) →
      ∀ a : ℕ → ArithmeticFunction ℝ,(∀ i,a i 1=0) →
      (∀ i p,p.Prime → a i p=roughOrdinaryPrimeWeight (Y i) p) →
      ∀ B : ℝ,0 ≤ B → (∀ q,¬q.Prime → (∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) →
      Chebyshev.theta (H N)-Chebyshev.theta (min (max (H 0) (Y N)) (H N)) ≤
        (∑ i ∈ range N,|headAt (a (i+1)) (Y (i+1)) (H (i+1))-headAt (a i) (Y i) (H i)|)+
        ((Y N:ℝ)-Y 0)*Real.log (H N)+K*B*deletionPrice s (Y N)*(H N:ℝ)^s := by
  obtain ⟨K,k0,cap⟩ := common_edits_on_unchanged_walls strip upper
  refine ⟨K,k0,fun N Y H mono heights steps a unit ordinary B bp variation => ?_⟩
  let b := nextAtSameWall Y a
  let P := fun i => headAt (a i) (Y i) (H i)
  let D := fun i => |headAt (b i) (Y i) (H i)-headAt (a i) (Y i) (H i)|
  let g := fun p : ℕ => if p.Prime ∧ Y N<p then Real.log p else 0
  let G := fun t : ℕ => ∑ p ∈ Ioc 0 t,g p
  have totalEdits := cap N Y H mono heights a ordinary B bp variation
  have step (i : ℕ) (hi : i ∈ range N) : G (H (i+1))-G (H i) ≤
      |P (i+1)-P i|+((Y (i+1):ℝ)-Y i)*Real.log (H N)+D i := by
    let p := H (i+1)
    have iN : i+1 ≤ N := mem_range.mp hi
    have pN : p ≤ H N := heights iN
    have wall := mono (Nat.le_succ i)
    have z := mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr wall)) (Real.log_natCast_nonneg (H N))
    by_cases still : H (i+1)=H i
    · rw [still,sub_self]; exact add_nonneg (add_nonneg (abs_nonneg _) z) (abs_nonneg _)
    have arrival : H (i+1)=H i+1 := by
      have := heights (Nat.le_succ i)
      have := steps i (mem_range.mp hi)
      omega
    have jump : G (H (i+1))-G (H i)=g p := by
      dsimp only [G,p]; rw [arrival,sum_Ioc_succ_top (Nat.zero_le _),add_sub_cancel_left]
    rw [jump]
    by_cases marked : p.Prime ∧ Y N<p
    · change (if p.Prime ∧ Y N<p then Real.log p else 0) ≤ _
      rw [if_pos marked]
      by_cases eq : Y (i+1)=Y i
      · have high := (mono iN).trans_lt marked.2
        have primeValue : a (i+1) p=Real.log p := by
          rw [ordinary _ _ marked.1]
          change (if p.Prime ∧ Y (i+1)<p then Real.log p else 0)=_
          exact if_pos ⟨marked.1,high⟩
        have arriving := add_one_coefficient (a (i+1)) (Y (i+1)) (H i)
        rw [←arrival] at arriving
        rw [coefficient_at_an_arriving_prime _ _ (unit _) marked.1,primeValue,eq] at arriving
        have adj : P (i+1)-P i=(headAt (b i) (Y i) (H i)-headAt (a i) (Y i) (H i))+Real.log p := by
          change headAt (a (i+1)) (Y (i+1)) (H (i+1))-headAt (a i) (Y i) (H i)=_
          rw [eq,arriving]; simp only [b,nextAtSameWall,if_pos eq]; ring
        have tri := abs_sub (P (i+1)-P i) (headAt (b i) (Y i) (H i)-headAt (a i) (Y i) (H i))
        rw [show P (i+1)-P i-(headAt (b i) (Y i) (H i)-headAt (a i) (Y i) (H i))=Real.log p by rw [adj]; ring,
          abs_of_nonneg (Real.log_natCast_nonneg _)] at tri
        dsimp only [D]
        linarith only [tri,z]
      · have inc : (Y i:ℝ)+1 ≤ Y (i+1) := by exact_mod_cast (show Y i+1 ≤ Y (i+1) from lt_of_le_of_ne wall (Ne.symm eq))
        have log := Real.log_le_log (Nat.cast_pos.mpr marked.1.pos) (Nat.cast_le.mpr pN)
        have cost := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (Y (i+1):ℝ)-Y i by linarith only [inc]) (Real.log_natCast_nonneg (H N))
        exact log.trans (by linarith only [cost,abs_nonneg (P (i+1)-P i),show 0 ≤ D i from abs_nonneg _])
    · change (if p.Prime ∧ Y N<p then Real.log p else 0) ≤ _
      rw [if_neg marked]
      exact add_nonneg (add_nonneg (abs_nonneg _) z) (abs_nonneg _)
  have summed := sum_le_sum step
  rw [sum_add_distrib,sum_add_distrib,←sum_mul,sum_range_sub,sum_range_sub] at summed
  have θ : G (H N)-G (H 0)=Chebyshev.theta (H N)-Chebyshev.theta (min (max (H 0) (Y N)) (H N)) := by
    rw [GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits.theta_sub_theta (min_le_right ..)]
    have consecutive := sum_Ioc_consecutive g (Nat.zero_le (H 0)) (heights (Nat.zero_le N))
    have eq : G (H N)-G (H 0)=∑ q ∈ Ioc (H 0) (H N),g q :=
      sub_eq_of_eq_add (consecutive.symm.trans (add_comm ..))
    have split : Ioc (min (max (H 0) (Y N)) (H N)) (H N)=(Ioc (H 0) (H N)).filter (Y N<·) := by
      ext p; simp only [mem_Ioc,mem_filter]; omega
    rw [eq,split,sum_filter]
    exact sum_congr rfl (fun p _ => by by_cases pr : p.Prime <;> by_cases high : Y N<p <;> simp [g,pr,high])
  rw [←θ]
  change (∑ i ∈ range N,D i) ≤ K*B*deletionPrice s (Y N)*(H N:ℝ)^s at totalEdits
  exact summed.trans (by linarith only [totalEdits])

private theorem log_mono_on_integers {m n : ℕ} (leq : m ≤ n) : Real.log m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with rfl | pos
  · simpa only [Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg n
  exact Real.log_le_log (Nat.cast_pos.mpr pos) (Nat.cast_le.mpr leq)

/-- The variation upper bound also permits proper-power weights supported
below the current sieve. A change of wall is charged at its two endpoints. -/
theorem upper_variation_at_moving_prime_walls {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s) (upper : s ≤ 1) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ N : ℕ,∀ Y H : ℕ → ℕ,Monotone Y → Monotone H →
      (∀ i,i<N → H (i+1) ≤ H i+1) → ∀ a : ℕ → ArithmeticFunction ℝ,
      (∀ i q,|a i q| ≤ vonMangoldt q) → (∀ i p,p.Prime → a i p=roughOrdinaryPrimeWeight (Y i) p) →
      ∀ B : ℝ,0 ≤ B → (∀ q,¬q.Prime → (∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) →
      (∑ i ∈ range N,|headAt (a (i+1)) (Y (i+1)) (H (i+1))-headAt (a i) (Y i) (H i)|) ≤
        (1+2*(Y N:ℝ))*(H N:ℝ)*Real.log (H N)+K*B*deletionPrice s (Y N)*(H N:ℝ)^s := by
  obtain ⟨K,k0,common⟩ := common_edits_on_unchanged_walls strip upper
  refine ⟨K,k0,fun N Y H walls heights stepH a dom fixed B bp changes => ?_⟩
  let P := fun i => headAt (a i) (Y i) (H i)
  let D := fun i => |headAt (nextAtSameWall Y a i) (Y i) (H i)-headAt (a i) (Y i) (H i)|
  let L := Real.log (H N:ℝ)
  let U := (H N:ℝ)*L
  have l0 : 0 ≤ L := Real.log_natCast_nonneg _
  have u0 : 0 ≤ U := mul_nonneg (Nat.cast_nonneg _) l0
  have size (i : ℕ) (hin : i ≤ N) : |P i| ≤ U := by
    have r := rough_interpolation_price (dom i) (Y i) (H i) (H i)
    rw [rough_head_and_interior,add_sub_cancel_left,min_self] at r
    exact r.trans (mul_le_mul (Nat.cast_le.mpr (heights hin)) (log_mono_on_integers (heights hin))
      (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
  have per (i : ℕ) (hi : i ∈ range N) : |P (i+1)-P i| ≤
      ((H (i+1):ℝ)-H i)*L+((Y (i+1):ℝ)-Y i)*(2*U)+D i := by
    have iN : i+1 ≤ N := mem_range.mp hi
    have hstep := heights (Nat.le_succ i)
    have h0 := mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hstep)) l0
    by_cases eq : Y (i+1)=Y i
    · have move : |headAt (a (i+1)) (Y i) (H (i+1))-headAt (a (i+1)) (Y i) (H i)| ≤
          ((H (i+1):ℝ)-H i)*L := by
        by_cases stop : H (i+1)=H i
        · simp [stop]
        have next : H (i+1)=H i+1 := by have := stepH i (mem_range.mp hi); omega
        rw [next,add_one_coefficient,add_sub_cancel_left,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_mul]
        exact (rough_coefficient_le_log (dom (i+1)) (Y i) (H i+1)).trans
          (log_mono_on_integers ((le_of_eq next.symm).trans (heights iN)))
      have tri := abs_sub_le (headAt (a (i+1)) (Y i) (H (i+1)))
        (headAt (a (i+1)) (Y i) (H i)) (P i)
      change |headAt (a (i+1)) (Y (i+1)) (H (i+1))-P i| ≤ _
      rw [eq,sub_self,zero_mul,add_zero]
      dsimp only [D,nextAtSameWall]
      rw [if_pos eq]
      exact tri.trans (add_le_add_right move _)
    · have gap := Nat.cast_le.mpr (α := ℝ) (show Y i+1 ≤ Y (i+1) from lt_of_le_of_ne (walls (Nat.le_succ i)) (Ne.symm eq))
      rw [Nat.cast_add,Nat.cast_one] at gap
      have debt := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (Y (i+1):ℝ)-Y i by linarith only [gap])
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) u0)
      have endpoints := (abs_sub (P (i+1)) (P i)).trans (add_le_add (size _ iN) (size _ (Nat.le_of_succ_le iN)))
      linarith only [endpoints,debt,h0,show 0 ≤ D i from abs_nonneg _]
  have sum := sum_le_sum per
  simp only [sum_add_distrib,←sum_mul,sum_range_sub] at sum
  have edit := common N Y H walls heights a fixed B bp changes
  change (∑ i ∈ range N,D i) ≤ _ at edit
  have start := mul_nonneg (Nat.cast_nonneg (α := ℝ) (H 0)) l0
  have wstart := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Y 0)) u0
  change (∑ i ∈ range N,|P (i+1)-P i|) ≤ (1+2*(Y N:ℝ))*(H N:ℝ)*L+_
  dsimp only [U] at *
  linarith only [sum,edit,start,wstart]

/-- Total observed variation of the signed head on the polynomial height path. -/
def polynomialHeadVariation (α : ℝ) (a : ℕ → ArithmeticFunction ℝ) (N : ℕ) :=
  let P := fun i : ℕ => headAt (a i) (logSquareCutoff i) ⌊(i:ℝ)^α⌋₊
  ∑ i ∈ range N,|P (i+1)-P i|

private abbrev powerHeight (α : ℝ) (n : ℕ) := ⌊(n:ℝ)^α⌋₊

private theorem power_height_facts {α : ℝ} (ap : 0<α) (small : α ≤ 1) :
    Monotone (powerHeight α) ∧ (∀ n,powerHeight α (n+1) ≤ powerHeight α n+1) ∧
      Tendsto (powerHeight α) atTop atTop ∧
      ∀ᶠ n : ℕ in atTop,(n:ℝ)^α/2 ≤ powerHeight α n := by
  have mono : Monotone (powerHeight α) := fun _ _ leq => Nat.floor_le_floor
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr leq) ap.le)
  have step (n : ℕ) : powerHeight α (n+1) ≤ powerHeight α n+1 := by
    have add := Real.rpow_add_le_add_rpow (Nat.cast_nonneg n) (zero_le_one : (0:ℝ) ≤ 1) ap.le small
    rw [Real.one_rpow] at add
    simpa only [powerHeight,Nat.cast_add,Nat.cast_one,Nat.floor_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) α)]
      using Nat.floor_le_floor add
  have grows : Tendsto (fun n : ℕ => (n:ℝ)^α) atTop atTop := (tendsto_rpow_atTop ap).comp tendsto_natCast_atTop_atTop
  have wall : Tendsto (powerHeight α) atTop atTop := tendsto_atTop.mpr (fun k =>
    (grows.eventually_ge_atTop (k:ℝ)).mono (fun _ high => Nat.le_floor high))
  refine ⟨mono,step,wall,?_⟩
  filter_upwards [grows.eventually_ge_atTop 2] with n two
  change (n:ℝ)^α/2 ≤ (⌊(n:ℝ)^α⌋₊:ℝ)
  linarith only [two,Nat.lt_floor_add_one ((n:ℝ)^α)]

private theorem polynomial_path_allowance {s α η : ℝ} (strip : 1/2<s) (small : α ≤ 1) (ep : 0<η) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ n : ℕ in atTop,
      (1+(logSquareCutoff n:ℝ))*(1+Real.log (powerHeight α n))*deletionPrice s (logSquareCutoff n) ≤ A*(n:ℝ)^η := by
  let h := η/2
  have hp : 0<h := half_pos ep
  have sp := (by norm_num : (0:ℝ)<1/2).trans strip
  refine ⟨1+1/h,by positivity,?_⟩
  filter_upwards [log_square_deletion_cost strip hp,eventually_ge_atTop (1:ℕ)] with n euler np
  let E := deletionPrice s (logSquareCutoff n)
  let y : ℝ := logSquareCutoff n
  let t := powerHeight α n
  have n1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr np
  have n0 := zero_lt_one.trans_le n1
  have one : 1 ≤ E := deletionPrice_one_le sp _
  have esq : E ≤ E^2 := by nlinarith only [one,sq_nonneg (E-1)]
  have yc : (1+y)*E ≤ (n:ℝ)^h := by
    have cut := mul_le_mul_of_nonneg_left esq (by dsimp [y]; positivity : 0 ≤ 1+y)
    exact cut.trans (by simpa only [add_comm (1:ℝ)] using euler)
  have index : t ≤ n := Nat.cast_le.mp ((Nat.floor_le (Real.rpow_nonneg n0.le α)).trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le n1 small))
  have log := (log_mono_on_integers index).trans (Real.log_le_rpow_div n0.le hp)
  have lc : 1+Real.log t ≤ (1+1/h)*(n:ℝ)^h := (add_le_add (Real.one_le_rpow n1 hp.le) log).trans_eq (by ring)
  have cap := mul_le_mul yc lc (by linarith only [Real.log_natCast_nonneg t] : 0 ≤ 1+Real.log t)
    (Real.rpow_nonneg n0.le _)
  calc _ = ((1+y)*E)*(1+Real.log t) := by ring
       _ ≤ (n:ℝ)^h*((1+1/h)*(n:ℝ)^h) := cap
       _ = _ := by rw [show η=h+h by dsimp only [h]; ring,Real.rpow_add n0]; ring

private theorem components_of_path_allowance {s : ℝ} (sp : 0<s) (y t : ℕ) :
    let P := (1+(y:ℝ))*(1+Real.log t)*deletionPrice s y
    (y:ℝ) ≤ P ∧ (y:ℝ)*Real.log t ≤ P ∧ deletionPrice s y ≤ P ∧
      (1+2*(y:ℝ))*Real.log t ≤ 2*P := by
  let E := deletionPrice s y
  let w : ℝ := y
  let L := Real.log (t:ℝ)
  have w0 : 0 ≤ w := Nat.cast_nonneg _
  have l0 : 0 ≤ L := Real.log_natCast_nonneg _
  have e1 : 1 ≤ E := deletionPrice_one_le sp _
  have lower := le_mul_of_one_le_right (mul_nonneg (by linarith only [w0] : 0 ≤ 1+w) (by linarith only [l0] : 0 ≤ 1+L)) e1
  have factors : 1 ≤ (1+w)*(1+L) := one_le_mul_of_one_le_of_one_le (by linarith only [w0]) (by linarith only [l0])
  have ec := le_mul_of_one_le_left (zero_le_one.trans e1) factors
  change w ≤ (1+w)*(1+L)*E ∧ w*L ≤ _ ∧ E ≤ _ ∧ (1+2*w)*L ≤ _
  exact ⟨by linarith only [lower,w0,l0,mul_nonneg w0 l0],by linarith only [lower,w0,l0],
    ec,by linarith only [lower,w0,l0]⟩

/-- The variation on the actual log-square path has precisely the height
exponent α. Both ordinary primes and the full Mangoldt weights qualify,
as do all dominated proper-power edits of bounded variation at each atom. -/
theorem polynomial_head_variation_has_the_height_exponent {α : ℝ} (ap : 0<α) (sm : α ≤ 1)
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ i q,|a i q| ≤ vonMangoldt q)
    (fix : ∀ i p,p.Prime → a i p=roughOrdinaryPrimeWeight (logSquareCutoff i) p)
    {B : ℝ} (bp : 0 ≤ B)
    (changes : ∀ N q,¬q.Prime → (∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) :
    (∀ᶠ N : ℕ in atTop,(N:ℝ)^α/8 ≤ polynomialHeadVariation α a N) ∧
      ∀ ε : ℝ,0<ε → PrefixPower (α+ε) (polynomialHeadVariation α a) := by
  let θ := RHTower.zetaZeroAbscissa
  let s := (θ+1)/2
  have strip : θ<1 := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths.trans_lt (by norm_num)
  have hs : θ<s := by dsimp only [s]; linarith only [strip]
  have su : s<1 := by dsimp only [s]; linarith only [strip]
  have half := RHTower.half_le_zetaZeroAbscissa.trans_lt hs
  have sp := (by norm_num : (0:ℝ)<1/2).trans half
  let H := powerHeight α
  let Y := logSquareCutoff
  let V := polynomialHeadVariation α a
  obtain ⟨inc,steps,top,scale⟩ := power_height_facts ap sm
  have unit (i : ℕ) : a i 1=0 := abs_eq_zero.mp (le_antisymm (by simpa using dom i 1) (abs_nonneg _))
  have hzero : H 0=0 := by simp [H,powerHeight,Real.zero_rpow ap.ne']
  have lowerTop : ∀ᶠ i : ℕ in atTop,(H i:ℝ)/2 ≤ Chebyshev.theta (H i) := by
    have main := (RHTower.tendsto_theta_div_self.comp (tendsto_natCast_atTop_atTop.comp top)).eventually_ge_const
      (by norm_num : (1/2:ℝ)<1)
    filter_upwards [main,top.eventually_ge_atTop 1] with i good ip
    have positive : 0<(H i:ℝ) := Nat.cast_pos.mpr ip
    have h := (le_div_iff₀ positive).mp good
    linarith only [h]
  constructor
  · let h := α*(1-s)/2
    have hp : 0<h := div_pos (mul_pos ap (sub_pos.mpr su)) (by norm_num)
    obtain ⟨K,k0,estimate⟩ := prime_arrivals_force_head_variation hs su.le
    obtain ⟨A,apos,price⟩ := polynomial_path_allowance (α := α) half sm hp
    let C := (Real.log 4+1+K*B)*A
    have grows : Tendsto (fun n : ℕ => (n:ℝ)^h) atTop atTop := (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
    filter_upwards [scale,price,lowerTop,top.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ),
      grows.eventually_ge_atTop (8*C)] with N halfScale paid main height np enough
    let n := (N:ℝ)
    let T := (H N:ℝ)
    let y := (Y N:ℝ)
    let P := (1+y)*(1+Real.log T)*deletionPrice s (Y N)
    have n0 : 0<n := Nat.cast_pos.mpr np
    have t1 : 1 ≤ T := Nat.one_le_cast.mpr height
    have tpower := Real.one_le_rpow t1 sp.le
    have P0 : 0 ≤ P := (Nat.cast_nonneg (α := ℝ) (Y N)).trans (components_of_path_allowance sp (Y N) (H N)).1
    have cmp := components_of_path_allowance sp (Y N) (H N)
    have pn : P ≤ P*T^s := le_mul_of_one_le_right P0 tpower
    have bad := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) (min (Y N) (H N)))
    have log0 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    have ybad := mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (min_le_left (Y N) (H N))).trans (cmp.1.trans pn)) log0
    have wall := mul_le_mul_of_nonneg_right (sub_le_self y (Nat.cast_nonneg (α := ℝ) (Y 0))) (Real.log_natCast_nonneg (H N))
    have edit := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cmp.2.2.1 (Real.rpow_nonneg (Nat.cast_nonneg _) s)) (mul_nonneg k0 bp)
    have observed := estimate N Y H logSquareCutoff_mono inc (fun i _ => steps i) a unit fix B bp (changes N)
    rw [hzero,Nat.zero_max] at observed
    have loss : T/2 ≤ V N+(Real.log 4+1+K*B)*(P*T^s) := by
      change Chebyshev.theta (H N)-Chebyshev.theta (min (Y N) (H N)) ≤ V N+
        (y-(Y 0:ℝ))*Real.log T+K*B*deletionPrice s (Y N)*T^s at observed
      linarith only [observed,bad,ybad,wall,cmp.2.1,pn,edit,main]
    have tp := Real.rpow_le_rpow (Nat.cast_nonneg (H N)) (Nat.floor_le (Real.rpow_nonneg n0.le α)) sp.le
    rw [←Real.rpow_mul n0.le] at tp
    have joint := mul_le_mul paid tp (Real.rpow_nonneg (Nat.cast_nonneg _) s) (mul_nonneg apos.le (Real.rpow_nonneg n0.le h))
    have mult := mul_le_mul_of_nonneg_left joint (by linarith only [log0,mul_nonneg k0 bp] : 0 ≤ Real.log 4+1+K*B)
    have limit := mul_le_mul_of_nonneg_right enough (Real.rpow_nonneg n0.le (h+α*s))
    have exp : h+(h+α*s)=α := by dsimp only [h]; ring
    rw [←Real.rpow_add n0,exp,Real.rpow_add n0] at limit
    dsimp only [C] at limit
    change n^α/2 ≤ T at halfScale
    change n^α/8 ≤ V N
    linarith only [loss,halfScale,mult,limit]
  · intro ε ep
    obtain ⟨K,k0,estimate⟩ := upper_variation_at_moving_prime_walls hs su.le
    obtain ⟨A,apos,price⟩ := polynomial_path_allowance (α := α) half sm ep
    apply prefixPower_of_eventual (C := (2+K*B)*A) (by simp [polynomialHeadVariation]) (add_pos ap ep)
    filter_upwards [price,top.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with N paid height np
    let n := (N:ℝ)
    let T := (H N:ℝ)
    let y := (Y N:ℝ)
    let P := (1+y)*(1+Real.log T)*deletionPrice s (Y N)
    have n0 : 0<n := Nat.cast_pos.mpr np
    have t1 : 1 ≤ T := Nat.one_le_cast.mpr height
    have tp : T^s ≤ T := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le t1 su.le
    have cmp := components_of_path_allowance sp (Y N) (H N)
    have P0 : 0 ≤ P := (Nat.cast_nonneg (α := ℝ) (Y N)).trans cmp.1
    have edit := mul_le_mul_of_nonneg_left (mul_le_mul cmp.2.2.1 tp (Real.rpow_nonneg (Nat.cast_nonneg _) s) P0) (mul_nonneg k0 bp)
    have wall := mul_le_mul_of_nonneg_right cmp.2.2.2 (Nat.cast_nonneg (α := ℝ) (H N))
    have result := estimate N Y H logSquareCutoff_mono inc (fun i _ => steps i) a dom fix B bp (changes N)
    change V N ≤ (1+2*y)*T*Real.log T+K*B*deletionPrice s (Y N)*T^s at result
    have size : T ≤ n^α := Nat.floor_le (Real.rpow_nonneg n0.le _)
    have cap := mul_le_mul paid size (Nat.cast_nonneg _) (mul_nonneg apos.le (Real.rpow_nonneg n0.le ε))
    have last := mul_le_mul_of_nonneg_left cap (by linarith only [mul_nonneg k0 bp] : 0 ≤ 2+K*B)
    have pos : 0 ≤ V N := sum_nonneg (fun _ _ => abs_nonneg _)
    change |V N| ≤ (2+K*B)*A*n^(α+ε)
    rw [abs_of_nonneg pos,Real.rpow_add n0]
    linarith only [result,wall,edit,last]

#print axioms polynomial_head_variation_has_the_height_exponent

#print axioms upper_variation_at_moving_prime_walls
#print axioms prime_arrivals_force_head_variation
end GaloisForLFunctions.RestrictedFactorizationCalculus
