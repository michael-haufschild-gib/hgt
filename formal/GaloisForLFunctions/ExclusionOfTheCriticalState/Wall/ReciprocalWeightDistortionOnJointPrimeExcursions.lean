import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand

/-!
# Reciprocal-square weights on joint prime excursions

The duality of a weight and its reciprocal in the quadratic Muckenhoupt
condition (Fang–Phan, Proposition 2.2) gives an exact price for replacing
the numerator weight by a constant. The price is a variance of the
numerators themselves and has a uniform bound on every multiplicative band.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Quadratic mass of a finite set of numerators. -/
def numeratorSquareMass (S : Finset ℕ) : ℝ := ∑ H ∈ S, (H:ℝ)^2

/-- The reciprocal-square mass occurring in the joint excursion moment. -/
def numeratorInverseMass (S : Finset ℕ) : ℝ := ∑ H ∈ S, 1/(H:ℝ)^2

private theorem reciprocal_cross {H J : ℕ} (hH : 0 < H) (hJ : 0 < J) :
    (((H:ℝ)^2-(J:ℝ)^2)/((H:ℝ)*J))^2 =
      (H:ℝ)^2*(1/(J:ℝ)^2) + (J:ℝ)^2*(1/(H:ℝ)^2) - 2 := by
  field_simp [show (H:ℝ)≠0 from Nat.cast_ne_zero.mpr hH.ne',
    show (J:ℝ)≠0 from Nat.cast_ne_zero.mpr hJ.ne']
  ring

/-- Twice the unnormalized quadratic weight defect is the sum of squared
pairwise distortions. This identity includes the empty set. -/
theorem numerator_weight_defect (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H) :
    ∑ H ∈ S, ∑ J ∈ S, (((H:ℝ)^2-(J:ℝ)^2)/((H:ℝ)*J))^2 =
      2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) := by
  have inner (H : ℕ) (hH : H ∈ S) :
      ∑ J ∈ S, (((H:ℝ)^2-(J:ℝ)^2)/((H:ℝ)*J))^2 =
        (H:ℝ)^2*numeratorInverseMass S + numeratorSquareMass S*(1/(H:ℝ)^2) - S.card*2 := by
    rw [sum_congr rfl (fun J hJ => reciprocal_cross (hS H hH) (hS J hJ)),
      sum_sub_distrib,sum_add_distrib,← mul_sum,← sum_mul,sum_const,nsmul_eq_mul]
    rfl
  rw [sum_congr rfl inner,sum_sub_distrib,sum_add_distrib,← sum_mul,← mul_sum,sum_const,nsmul_eq_mul]
  change numeratorSquareMass S * numeratorInverseMass S + numeratorSquareMass S * numeratorInverseMass S -
    (S.card:ℝ)*(S.card*2) = _
  ring

/-- Uniform bound for the distortion in a multiplicative numerator band.
The constant depends only on its two endpoints; squaring their difference
makes the deviation quadratic on short relative bands. -/
theorem numerator_band_distortion (S : Finset ℕ) {a b : ℝ} (ha : 0 < a)
    (hS : ∀ H ∈ S, a ≤ (H:ℝ) ∧ (H:ℝ) ≤ b) :
    4*(a*b)^2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) ≤
      (S.card:ℝ)^2*(b^2-a^2)^2 := by
  let P := numeratorSquareMass S
  let Q := numeratorInverseMass S
  have hp : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hq : 0 ≤ Q := sum_nonneg fun _ _ => by positivity
  have site (H : ℕ) (hH : H ∈ S) :
      (H:ℝ)^2+(a*b)^2*(1/(H:ℝ)^2) ≤ a^2+b^2 := by
    obtain ⟨hl,hu⟩ := hS H hH
    have hh := ha.trans_le hl
    have hx := mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha.le hl 2))
      (sub_nonneg.mpr (pow_le_pow_left₀ hh.le hu 2))
    field_simp [hh.ne']
    nlinarith only [hx]
  have h := sum_le_sum site
  rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul] at h
  change P+(a*b)^2*Q ≤ S.card*(a^2+b^2) at h
  have hs := mul_self_le_mul_self (add_nonneg hp (mul_nonneg (sq_nonneg _) hq)) h
  change 4*(a*b)^2*(P*Q-(S.card:ℝ)^2) ≤ _
  nlinarith only [hs,sq_nonneg (P-(a*b)^2*Q)]

private theorem numerator_regression_coordinates (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H)
    (g : ℕ → ℝ) (c : ℝ) :
    let Q := numeratorInverseMass S
    let n : ℝ := S.card
    let x (H : ℕ) := (g H-c)/(H:ℝ)
    let y (H : ℕ) := Q*(H:ℝ)-n/(H:ℝ)
    (∑ H ∈ S, x H*y H) = Q*(∑ H ∈ S, g H)-n*(∑ H ∈ S, g H/(H:ℝ)^2) ∧
      (∑ H ∈ S, y H^2) = Q*(numeratorSquareMass S*Q-n^2) := by
  intro Q n x y
  have cross (H : ℕ) (hH : H ∈ S) :
      x H*y H = Q*g H - n*(g H/(H:ℝ)^2) - Q*c + n*c*(1/(H:ℝ)^2) := by
    dsimp only [x,y]
    field_simp [show (H:ℝ)≠0 from Nat.cast_ne_zero.mpr (hS H hH).ne']
    ring
  have yy (H : ℕ) (hH : H ∈ S) :
      y H^2 = Q^2*(H:ℝ)^2 - 2*Q*n + n^2*(1/(H:ℝ)^2) := by
    dsimp only [y]
    field_simp [show (H:ℝ)≠0 from Nat.cast_ne_zero.mpr (hS H hH).ne']
    ring
  have dot : (∑ H ∈ S, x H*y H) = Q*(∑ H ∈ S, g H)-n*(∑ H ∈ S, g H/(H:ℝ)^2) := by
    rw [sum_congr rfl cross,sum_add_distrib,sum_sub_distrib,sum_sub_distrib,
      ← mul_sum,← mul_sum,← mul_sum,sum_const,nsmul_eq_mul]
    rw [← mul_sum]
    change _ - Q*(n*c) + n*c*Q = _
    ring
  have cost : (∑ H ∈ S, y H^2) = Q*(numeratorSquareMass S*Q-n^2) := by
    rw [sum_congr rfl yy,sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,sum_const,nsmul_eq_mul]
    rw [← mul_sum]
    change Q^2*numeratorSquareMass S - 2*Q*(n*n) + n^2*Q = _
    ring
  exact ⟨dot,cost⟩

/-- Exact covariance price of replacing reciprocal-square mass by counting
mass. Only the centered part of the observable contributes to the error. -/
theorem numerator_counting_covariance (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H) (g : ℕ → ℝ) (c : ℝ) :
    (numeratorInverseMass S*(∑ H ∈ S, g H) - S.card*(∑ H ∈ S, g H/(H:ℝ)^2))^2 ≤
      (∑ H ∈ S, ((g H-c)/(H:ℝ))^2) * (numeratorInverseMass S *
        (numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2)) := by
  obtain ⟨dot,cost⟩ := numerator_regression_coordinates S hS g c
  have cs := sum_mul_sq_le_sq_mul_sq S (fun H => (g H-c)/(H:ℝ))
    (fun H => numeratorInverseMass S*(H:ℝ)-(S.card:ℝ)/(H:ℝ))
  rw [dot,cost] at cs
  exact cs

/-- Exact residual after fitting an affine function of the squared numerator.
The linear coefficient in this quadratic is the counting-replacement error.
Taking its minimizing slope gives the part invisible to both measures. -/
theorem numerator_regression_remainder (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H)
    (g : ℕ → ℝ) (c t : ℝ) :
    let Q := numeratorInverseMass S
    let n : ℝ := S.card
    let B := Q*(∑ H ∈ S, g H)-n*(∑ H ∈ S, g H/(H:ℝ)^2)
    let D := Q*(numeratorSquareMass S*Q-n^2)
    (∑ H ∈ S, ((g H-c-t*(Q*(H:ℝ)^2-n))/(H:ℝ))^2) =
      (∑ H ∈ S, ((g H-c)/(H:ℝ))^2)-2*t*B+t^2*D := by
  intro Q n B D
  let x (H : ℕ) := (g H-c)/(H:ℝ)
  let y (H : ℕ) := Q*(H:ℝ)-n/(H:ℝ)
  obtain ⟨dot,cost⟩ := numerator_regression_coordinates S hS g c
  change (∑ H ∈ S, x H*y H)=B at dot
  change (∑ H ∈ S, y H^2)=D at cost
  have site (H : ℕ) (hh : H∈S) :
      ((g H-c-t*(Q*(H:ℝ)^2-n))/(H:ℝ))^2 =
        x H^2-2*t*(x H*y H)+t^2*y H^2 := by
    have he : (g H-c-t*(Q*(H:ℝ)^2-n))/(H:ℝ) = x H-t*y H := by
      dsimp only [x,y]
      field_simp [show (H:ℝ)≠0 from Nat.cast_ne_zero.mpr (hS H hh).ne']
    rw [he]
    ring
  rw [sum_congr rfl site,sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,dot,cost]

private theorem numerator_regression_spread_pos (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H)
    (hn : 1 < S.card) :
    0 < numeratorInverseMass S*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hn
  have hq : 0 < numeratorInverseMass S := by
    apply lt_of_lt_of_le (show 0 < 1/(i:ℝ)^2 by
      exact div_pos one_pos (pow_pos (Nat.cast_pos.mpr (hS i hi)) 2))
    exact single_le_sum (f := fun H : ℕ => 1/(H:ℝ)^2) (fun k _ => by positivity) hi
  apply mul_pos hq
  have ni : 0 < (i:ℝ) := Nat.cast_pos.mpr (hS i hi)
  have nj : 0 < (j:ℝ) := Nat.cast_pos.mpr (hS j hj)
  have ne : (i:ℝ)^2≠(j:ℝ)^2 := fun he => hij (Nat.cast_injective (R:=ℝ)
    ((sq_eq_sq₀ ni.le nj.le).mp he))
  let L (u v : ℕ) := (((u:ℝ)^2-(v:ℝ)^2)/((u:ℝ)*v))^2
  have hp : 0<L i j := sq_pos_of_ne_zero (div_ne_zero (sub_ne_zero.mpr ne)
    (mul_pos ni nj).ne')
  have hle : L i j ≤ ∑ u ∈ S, ∑ v ∈ S, L u v :=
    (single_le_sum (fun k _ => show 0≤L i k from sq_nonneg _) hj).trans
      (single_le_sum (fun u _ => sum_nonneg fun v _ => show 0≤L u v from sq_nonneg _) hi)
  have id := numerator_weight_defect S hS
  change (∑ u ∈ S, ∑ v ∈ S, L u v)=_ at id
  linarith only [hp,hle,id]

/-- At two or more distinct positive numerators, the bound is saturated
precisely by an affine function of squared numerator, centered at the
weighted mean and with its slope fixed by the observed discrepancy. -/
theorem numerator_counting_equality_iff_affine (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H)
    (hn : 1 < S.card) (g : ℕ → ℝ) (c : ℝ) :
    let Q := numeratorInverseMass S
    let n : ℝ := S.card
    let B := Q*(∑ H ∈ S, g H)-n*(∑ H ∈ S, g H/(H:ℝ)^2)
    let D := Q*(numeratorSquareMass S*Q-n^2)
    B^2=(∑ H ∈ S, ((g H-c)/(H:ℝ))^2)*D ↔
      ∀ H ∈ S, g H=c+(B/D)*(Q*(H:ℝ)^2-n) := by
  intro Q n B D
  have hd : 0<D := numerator_regression_spread_pos S hS hn
  let A := ∑ H ∈ S, ((g H-c)/(H:ℝ))^2
  let F (H : ℕ) := ((g H-c-(B/D)*(Q*(H:ℝ)^2-n))/(H:ℝ))^2
  have id := numerator_regression_remainder S hS g c (B/D)
  change (∑ H ∈ S, F H)=A-2*(B/D)*B+(B/D)^2*D at id
  have scale : (∑ H ∈ S, F H)*D=A*D-B^2 := by
    rw [id]
    field_simp [hd.ne']
    ring
  change B^2=A*D ↔ _
  have site (H : ℕ) (hh : H∈S) :
      F H=0 ↔ g H=c+(B/D)*(Q*(H:ℝ)^2-n) := by
    unfold F
    rw [sq_eq_zero_iff,div_eq_zero_iff,or_iff_left (Nat.cast_ne_zero.mpr (hS H hh).ne')]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · intro he H hh
    have whole : (∑ K ∈ S, F K)=0 := (mul_eq_zero.mp
      (scale.trans (sub_eq_zero.mpr he.symm))).resolve_right hd.ne'
    have bound := single_le_sum (fun K _ => show 0≤F K from sq_nonneg _) hh
    rw [whole] at bound
    exact (site H hh).mp (le_antisymm bound (sq_nonneg _))
  · intro h
    have whole := sum_eq_zero (s:=S) (fun H hh => (site H hh).mpr (h H hh))
    rw [whole,zero_mul] at scale
    linarith only [scale]

/-- On the actual set of joint excursions, a constant raw product has zero
counting-replacement error. In general its centered weighted second moment
and the geometric spread of the eligible numerators pay for the error. -/
theorem opposite_prime_counting_covariance (left : Bool) (s a g d T : ℝ) (k L : ℕ) (c : ℝ) :
    let S := largeOppositePrimeNumerators left s a g d T k L
    let value (H : ℕ) := (H:ℝ)^2*oppositePrimeProduct left s k L H
    (numeratorInverseMass S*(∑ H ∈ S, value H) -
      S.card*(∑ H ∈ S, oppositePrimeProduct left s k L H))^2 ≤
      (∑ H ∈ S, ((value H-c)/(H:ℝ))^2)*(numeratorInverseMass S*
        (numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2)) := by
  intro S value
  have hS (H : ℕ) (hH : H ∈ S) : 0 < H := by
    have h := (mem_filter.mp (mem_filter.mp hH).1).2.1
    exact Nat.cast_pos.mp ((Real.exp_pos T).trans_le h)
  have he (H : ℕ) (hH : H ∈ S) : value H/(H:ℝ)^2=oppositePrimeProduct left s k L H :=
    mul_div_cancel_left₀ _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (hS H hH).ne'))
  have hh := numerator_counting_covariance S hS value c
  rw [sum_congr rfl he] at hh
  exact hh

/-- Sum of the interior losses in the band inequality. Each endpoint
contributes zero, and every strictly interior positive numerator contributes
a positive amount. -/
def numeratorInteriorLoss (S : Finset ℕ) (a b : ℝ) : ℝ :=
  ∑ H ∈ S, (((H:ℝ)^2-a^2)*(b^2-(H:ℝ)^2))/(H:ℝ)^2

/-- Exact deficit in the reciprocal-square band inequality. The first
square measures imbalance of the two moments, and the second term charges
interior points of the band. -/
theorem numerator_band_deficit (S : Finset ℕ) (hS : ∀ H ∈ S, 0<H) (a b : ℝ) :
    let n : ℝ := S.card
    let P := numeratorSquareMass S
    let Q := numeratorInverseMass S
    let E := numeratorInteriorLoss S a b
    n^2*(b^2-a^2)^2-4*(a*b)^2*(P*Q-n^2) =
      (P-(a*b)^2*Q)^2 + E*(n*(a^2+b^2)+P+(a*b)^2*Q) := by
  intro n P Q E
  have site (H : ℕ) (hh : H ∈ S) :
      (((H:ℝ)^2-a^2)*(b^2-(H:ℝ)^2))/(H:ℝ)^2 =
        (a^2+b^2)-(H:ℝ)^2-(a*b)^2*(1/(H:ℝ)^2) := by
    field_simp [show (H:ℝ)≠0 from Nat.cast_ne_zero.mpr (hS H hh).ne']
    ring
  have he : E=n*(a^2+b^2)-P-(a*b)^2*Q := by
    change (∑ H ∈ S, _)=_
    rw [sum_congr rfl site,sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,←mul_sum]
    rfl
  rw [he]
  ring

/-- Equality forces every numerator to be a band endpoint, with equal
quadratic and scaled reciprocal mass. These two conditions also suffice. -/
theorem numerator_band_equality (S : Finset ℕ) (hn : S.Nonempty) {a b : ℝ}
    (ha : 0<a) (hS : ∀ H ∈ S, a≤(H:ℝ) ∧ (H:ℝ)≤b) :
    4*(a*b)^2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) =
        (S.card:ℝ)^2*(b^2-a^2)^2 ↔
      numeratorSquareMass S=(a*b)^2*numeratorInverseMass S ∧
        ∀ H ∈ S, (H:ℝ)=a ∨ (H:ℝ)=b := by
  let term (H : ℕ) := (((H:ℝ)^2-a^2)*(b^2-(H:ℝ)^2))/(H:ℝ)^2
  have hpos (H : ℕ) (hh : H∈S) := ha.trans_le (hS H hh).1
  have ht (H : ℕ) (hh : H∈S) : 0≤term H := by
    have hs := hS H hh
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha.le hs.1 2))
      (sub_nonneg.mpr (pow_le_pow_left₀ (hpos H hh).le hs.2 2))) (sq_nonneg _)
  have id := numerator_band_deficit S (fun H hh => Nat.cast_pos.mp (hpos H hh)) a b
  let P := numeratorSquareMass S
  let Q := numeratorInverseMass S
  let C := (S.card:ℝ)*(a^2+b^2)+P+(a*b)^2*Q
  have hP : 0≤P := sum_nonneg fun _ _ => sq_nonneg _
  have hQ : 0≤Q := sum_nonneg fun _ _ => by positivity
  have hC : 0<C := by
    have hn' : 0<(S.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr hn)
    dsimp only [C]
    positivity
  change _ = (P-(a*b)^2*Q)^2 + (∑ H ∈ S, term H)*C at id
  constructor
  · intro he
    rw [he,sub_self] at id
    have hsum := sum_nonneg ht
    have h₀ := mul_nonneg hsum hC.le
    have hsquare := sq_nonneg (P-(a*b)^2*Q)
    have eq := sq_eq_zero_iff.mp (show (P-(a*b)^2*Q)^2=0 by linarith only [id,h₀,hsquare])
    refine ⟨sub_eq_zero.mp eq,fun H hh => ?_⟩
    have allzero : ∑ J ∈ S, term J = 0 := (mul_eq_zero.mp
      (show (∑ J ∈ S, term J)*C=0 by linarith only [id,hsquare,h₀])).resolve_right hC.ne'
    have single := single_le_sum ht hh
    rw [allzero] at single
    have zero := le_antisymm single (ht H hh)
    have edge : ((H:ℝ)^2-a^2)*(b^2-(H:ℝ)^2)=0 := by
      change _ / (H:ℝ)^2=0 at zero
      exact (div_eq_zero_iff.mp zero).resolve_right (pow_ne_zero 2 (hpos H hh).ne')
    rcases mul_eq_zero.mp edge with h|h
    · left
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp h)).resolve_right
        (by linarith only [ha,hpos H hh])
    · right
      exact ((sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp h)).resolve_right
        (by linarith only [(hS H hh).2,hpos H hh])).symm
  · rintro ⟨eq,ends⟩
    have zero : ∑ J ∈ S, term J = 0 := sum_eq_zero (fun H hh => by
      rcases ends H hh with h|h <;> simp [term,h])
    change P=(a*b)^2*Q at eq
    have square_zero : (P-(a*b)^2*Q)^2 = 0 := by rw [eq,sub_self]; norm_num
    rw [zero,zero_mul,add_zero,square_zero] at id
    linarith only [id]

/-- Three distinct numerators force strict improvement over the uniform
band constant, even if both endpoints belong to the sample. -/
theorem numerator_band_strict_of_three (S : Finset ℕ) (hn : 3≤S.card) {a b : ℝ}
    (ha : 0<a) (hS : ∀ H ∈ S, a≤(H:ℝ) ∧ (H:ℝ)≤b) :
    4*(a*b)^2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) <
      (S.card:ℝ)^2*(b^2-a^2)^2 := by
  apply (numerator_band_distortion S ha hS).lt_of_ne
  intro he
  have ends := ((numerator_band_equality S (card_pos.mp (by omega)) ha hS).mp he).2
  have sub : S.image (fun n : ℕ => (n:ℝ)) ⊆ {a,b} := by
    intro t ht
    obtain ⟨n,hh,rfl⟩ := mem_image.mp ht
    simpa only [mem_insert,mem_singleton] using ends n hh
  have hc := (card_le_card sub).trans card_le_two
  rw [card_image_of_injective _ (Nat.cast_injective (R:=ℝ))] at hc
  omega

/-- The band constant is exact for the two distinct integer endpoints
with counting measure. -/
theorem numerator_two_endpoints_sharp {m n : ℕ} (hm : 0 < m) (h : m < n) :
    let S : Finset ℕ := {m,n}
    4*((m:ℝ)*n)^2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) =
      (S.card:ℝ)^2*((n:ℝ)^2-(m:ℝ)^2)^2 := by
  intro S
  have hmn : m∉({n}:Finset ℕ) := fun e => h.ne (mem_singleton.mp e)
  have hn := hm.trans h
  simp only [S,numeratorSquareMass,numeratorInverseMass,sum_insert hmn,sum_singleton,
    card_insert_of_notMem hmn,card_singleton,Nat.cast_ofNat]
  field_simp [show (m:ℝ)≠0 from Nat.cast_ne_zero.mpr hm.ne',
    show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne']
  ring


end GaloisForLFunctions.ExclusionOfTheCriticalState
