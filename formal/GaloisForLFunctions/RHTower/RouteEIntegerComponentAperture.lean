import GaloisForLFunctions.RHTower.MobiusReciprocalMarkerPrimeCapacity
import GaloisForLFunctions.RHTower.RouteEPrimeActivationCompleteHistogramApertureNoGo
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerSubpowerSchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integer aperture of complete multiplicative cells

Three independently varying positive integer factors force a corner span `W` with
`27 * L^2 ≤ W^3`, where `L` is the lower product. The exponent and constant are
sharp for general integer factor cubes. This excludes three nonconstant integer
components in complete singleton histogram cells at the actual growing marker
window. It does not estimate the mass of incomplete cells or signed covariance.
-/

open Filter Topology Finset
open scoped BigOperators
noncomputable section
namespace RHTower.IntegerCubeAperture

private theorem amgm_min (x y z : ℝ) (hz : 0 ≤ z) (hzx : z ≤ x) (hzy : z ≤ y) :
    27*x*y*z ≤ (x+y+z)^3 := by
  have hs : 0 ≤ x+y-2*z := by linarith
  have h1 := pow_nonneg hs 3
  have h2 := mul_nonneg hz (sq_nonneg (x-y))
  have h3 := mul_nonneg hz (sq_nonneg (x-z))
  have h4 := mul_nonneg hz (sq_nonneg (y-z))
  nlinarith only [h1,h2,h3,h4]

private theorem amgm_three (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27*x*y*z ≤ (x+y+z)^3 := by
  rcases le_total x y with hxy | hyx
  · rcases le_total x z with hxz | hzx
    · convert amgm_min y z x hx hxy hxz using 1 <;> ring
    · exact amgm_min x y z hz hzx (hzx.trans hxy)
  · rcases le_total y z with hyz | hzy
    · convert amgm_min x z y hy hyx hyz using 1 <;> ring
    · exact amgm_min x y z hz (hzy.trans hyx) hzy

private theorem amgm_three_nat (x y z : ℕ) : 27*x*y*z ≤ (x+y+z)^3 := by
  exact_mod_cast amgm_three (x:ℝ) (y:ℝ) (z:ℝ) (by positivity) (by positivity) (by positivity)

/-- Integer increments force a cubic lower bound for a three-axis product span. -/
theorem three_axis_span (a b d A B D : ℕ) (ha : a < A) (hb : b < B) (hd : d < D) :
    27*(a*b*d)^2 ≤ (A*B*D-a*b*d)^3 := by
  have hp : (a+1)*(b+1)*(d+1) ≤ A*B*D :=
    Nat.mul_le_mul (Nat.mul_le_mul ha hb) hd
  have he : (a+1)*(b+1)*(d+1) = a*b*d+(a*b+a*d+b*d)+a+b+d+1 := by ring
  have hs : a*b+a*d+b*d ≤ A*B*D-a*b*d := by omega
  calc
    27*(a*b*d)^2 = 27*(a*b)*(a*d)*(b*d) := by ring
    _ ≤ (a*b+a*d+b*d)^3 := amgm_three_nat _ _ _
    _ ≤ (A*B*D-a*b*d)^3 := by gcongr

theorem three_axis_span_spectator (c a b d A B D : ℕ)
    (ha : a < A) (hb : b < B) (hd : d < D) :
    27*c*(c*a*b*d)^2 ≤ (c*(A*B*D-a*b*d))^3 := by
  calc
    27*c*(c*a*b*d)^2 = c^3*(27*(a*b*d)^2) := by ring
    _ ≤ c^3*(A*B*D-a*b*d)^3 := Nat.mul_le_mul_left _ (three_axis_span a b d A B D ha hb hd)
    _ = (c*(A*B*D-a*b*d))^3 := by ring

theorem three_axis_window (c a b d A B D X H : ℕ)
    (hc : 1 ≤ c) (ha : a < A) (hb : b < B) (hd : d < D)
    (hlower : X ≤ c*a*b*d) (hupper : c*A*B*D ≤ X+H) :
    27*X^2 ≤ H^3 := by
  have hp : a*b*d ≤ A*B*D := Nat.mul_le_mul (Nat.mul_le_mul ha.le hb.le) hd.le
  have he : c*(A*B*D-a*b*d)+c*a*b*d = c*A*B*D := by
    calc
      _ = c*((A*B*D-a*b*d)+a*b*d) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hp]; ring
  have hs : c*(A*B*D-a*b*d) ≤ H := by omega
  calc
    27*X^2 ≤ 27*(c*a*b*d)^2 := by gcongr
    _ ≤ 27*c*(c*a*b*d)^2 := by gcongr; omega
    _ ≤ (c*(A*B*D-a*b*d))^3 := three_axis_span_spectator c a b d A B D ha hb hd
    _ ≤ H^3 := by gcongr

/-- Selecting any three changing factors preserves the span bound in any dimension. -/
theorem product_span_of_three_changes {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℕ)
    (ha : ∀ i ∈ s, 1 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hcard : 2 < (s.filter fun i => a i < b i).card) :
    27*(∏ i ∈ s, a i)^2 ≤ ((∏ i ∈ s, b i)-(∏ i ∈ s, a i))^3 := by
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp hcard
  obtain ⟨his,hiab⟩ := mem_filter.mp hi
  obtain ⟨hjs,hjab⟩ := mem_filter.mp hj
  obtain ⟨hks,hkab⟩ := mem_filter.mp hk
  let t : Finset ι := {i,j,k}
  have hts : t ⊆ s := by
    intro l hl
    rcases (show l=i ∨ l=j ∨ l=k from by simpa [t] using hl) with rfl | rfl | rfl
    · exact his
    · exact hjs
    · exact hks
  let c := ∏ l ∈ s \ t, a l
  have hc : 1 ≤ c := Nat.succ_le_of_lt (Finset.prod_pos fun l hl => ha l (mem_sdiff.mp hl).1)
  have hsplit (f : ι → ℕ) :
      (∏ l ∈ s \ t, f l)*f i*f j*f k = ∏ l ∈ s, f l := by
    have he := Finset.prod_sdiff (f := f) hts
    simpa [t,hij,hik,hjk,mul_assoc] using he
  have hupper : c*b i*b j*b k ≤ ∏ l ∈ s, b l := by
    rw [← hsplit b]
    dsimp [c]
    gcongr with l hl
    exact hab l (mem_sdiff.mp hl).1
  have hprod : (∏ l ∈ s, a l) ≤ ∏ l ∈ s, b l := Finset.prod_le_prod' hab
  have h := three_axis_window c (a i) (a j) (a k) (b i) (b j) (b k)
    (∏ l ∈ s, a l) ((∏ l ∈ s, b l)-(∏ l ∈ s, a l))
    hc hiab hjab hkab (hsplit a).symm.le (by omega)
  exact h

theorem at_most_two_changes {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℕ) (X H : ℕ)
    (ha : ∀ i ∈ s, 1 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hlower : X ≤ ∏ i ∈ s, a i) (hupper : (∏ i ∈ s, b i) ≤ X+H)
    (hwidth : H^3 < 27*X^2) :
    (s.filter fun i => a i < b i).card ≤ 2 := by
  by_contra hn
  have he := product_span_of_three_changes s a b ha hab (by omega)
  have hl : 27*X^2 ≤ 27*(∏ i ∈ s, a i)^2 := by gcongr
  have hs : (∏ i ∈ s, b i)-(∏ i ∈ s, a i) ≤ H := by omega
  have hu : ((∏ i ∈ s, b i)-(∏ i ∈ s, a i))^3 ≤ H^3 := by gcongr
  omega

/-- Sharp leading constant for integer cubes; no Möbius admissibility is asserted. -/
theorem unit_increment_sharpness :
    Tendsto (fun n : ℕ =>
      (((((n+2)^3-(n+1)^3 : ℕ) : ℝ)^3)/((n+1:ℕ):ℝ)^6)) atTop (𝓝 27) := by
  have ht : Tendsto (fun n : ℕ => (((n+1:ℕ):ℝ))⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hconst : Tendsto (fun _ : ℕ => (3:ℝ)) atTop (𝓝 3) := tendsto_const_nhds
  have hh := ((hconst.add (hconst.mul ht)).add (ht.pow 2)).pow 3
  have he (n : ℕ) :
      (((((n+2)^3-(n+1)^3 : ℕ) : ℝ)^3)/((n+1:ℕ):ℝ)^6) =
        (3+3*(((n+1:ℕ):ℝ))⁻¹+((((n+1:ℕ):ℝ))⁻¹)^2)^3 := by
    have hn : (n+1)^3 ≤ (n+2)^3 := by gcongr; omega
    rw [Nat.cast_sub hn]
    push_cast
    field_simp
    ring
  convert hh.congr (fun n => (he n).symm) using 1
  norm_num

theorem at_most_two_changes_real_window {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℕ) (X H : ℝ)
    (ha : ∀ i ∈ s, 1 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hX : 0 ≤ X) (_hH : 0 ≤ H)
    (hlower : X ≤ ((∏ i ∈ s, a i : ℕ):ℝ))
    (hupper : ((∏ i ∈ s, b i : ℕ):ℝ) ≤ X+H)
    (hwidth : H^3 < 27*X^2) :
    (s.filter fun i => a i < b i).card ≤ 2 := by
  by_contra hn
  have hprod : (∏ i ∈ s, a i) ≤ ∏ i ∈ s, b i := Finset.prod_le_prod' hab
  have he : 27*(((∏ i ∈ s, a i : ℕ):ℝ))^2 ≤
      (((∏ i ∈ s, b i : ℕ):ℝ)-((∏ i ∈ s, a i : ℕ):ℝ))^3 := by
    rw [← Nat.cast_sub hprod]
    exact_mod_cast product_span_of_three_changes s a b ha hab (by omega)
  have hl : 27*X^2 ≤ 27*(((∏ i ∈ s, a i : ℕ):ℝ))^2 := by gcongr
  have hs : ((∏ i ∈ s, b i : ℕ):ℝ)-((∏ i ∈ s, a i : ℕ):ℝ) ≤ H := by linarith
  have hzero : (0:ℝ) ≤ ((∏ i ∈ s, b i : ℕ):ℝ)-((∏ i ∈ s, a i : ℕ):ℝ) := by
    exact_mod_cast Nat.zero_le ((∏ i ∈ s, b i)-(∏ i ∈ s, a i))
  have hu : (((∏ i ∈ s, b i : ℕ):ℝ)-((∏ i ∈ s, a i : ℕ):ℝ))^3 ≤ H^3 := by gcongr
  linarith

private def cornerHistory (n M : ℕ) (choice : Fin n → Bool) :
    RouteEComponentHistory (fun _ : Fin n => Bool) (M+2) :=
  fun r c => routeEPrimeActivationSeed n M
    (if choice c then r else Equiv.swap (0:Fin (M+2)) 1 r) c

private theorem cornerHistory_mem (n M : ℕ) (choice : Fin n → Bool) :
    cornerHistory n M choice ∈ routeEComponentHistogramCell (fun _ : Fin n => Bool) (M+2)
      (routeEComponentHistoryLabel (fun _ : Fin n => Bool) (routeEPrimeActivationSeed n M)) := by
  simp only [routeEComponentHistogramCell,mem_filter,mem_univ,true_and]
  intro c
  cases h : choice c
  · simp only [cornerHistory,h,Bool.false_eq_true,↓reduceIte,routeEComponentHistoryLabel]
    exact routeE_tupleHistogram_comp_perm (fun r => routeEPrimeActivationSeed n M r c)
      (Equiv.swap (0:Fin (M+2)) 1)
  · simp [cornerHistory,h,routeEComponentHistoryLabel]

private theorem cornerHistory_receiver (n M : ℕ) (choice : Fin n → Bool)
    (value : Fin n → Bool → ℕ) :
    routeEComponentSlotReceiver (fun _ : Fin n => Bool) (fun c b => (value c b:ℝ))
      (cornerHistory n M choice) 0 = ((∏ c, value c (choice c) : ℕ):ℝ) := by
  push_cast
  unfold routeEComponentSlotReceiver
  apply prod_congr rfl
  intro c hc
  cases h : choice c <;> simp [cornerHistory,h,routeEPrimeActivationSeed]

/-- Every binary corner occurs in the literal complete singleton histogram cell. -/
theorem complete_histogram_integer_components_at_most_two
    (n M : ℕ) (value : Fin n → Bool → ℕ) (X H : ℝ)
    (hvalue : ∀ c b, 1 ≤ value c b) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hwidth : (2*H)^3 < 27*(X-H)^2)
    (haperture : ∀ h ∈ routeEComponentHistogramCell (fun _ : Fin n => Bool) (M+2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool) (routeEPrimeActivationSeed n M)),
      ∀ r, routeEComponentSlotReceiver (fun _ : Fin n => Bool) (fun c b => (value c b:ℝ))
        h r ∈ Set.Icc (X-H) (X+H)) :
    (univ.filter fun c => value c false ≠ value c true).card ≤ 2 := by
  let a : Fin n → ℕ := fun c => min (value c false) (value c true)
  let b : Fin n → ℕ := fun c => max (value c false) (value c true)
  let low : Fin n → Bool := fun c => if value c false ≤ value c true then false else true
  let high : Fin n → Bool := fun c => if value c false ≤ value c true then true else false
  have hlo (c : Fin n) : value c (low c) = a c := by
    dsimp [low,a]
    split_ifs with h <;> simp [min_def,h]
  have hhi (c : Fin n) : value c (high c) = b c := by
    dsimp [high,b]
    split_ifs with h <;> simp [max_def,h]
  have hlower := (haperture (cornerHistory n M low) (cornerHistory_mem n M low) 0).1
  have hupper := (haperture (cornerHistory n M high) (cornerHistory_mem n M high) 0).2
  rw [cornerHistory_receiver] at hlower hupper
  simp only [hlo] at hlower
  simp only [hhi] at hupper
  have hresult := at_most_two_changes_real_window univ a b (X-H) (2*H)
    (fun c _ => le_min (hvalue c false) (hvalue c true))
    (fun c _ => min_le_max) (by linarith) (by positivity)
    hlower (by linarith) hwidth
  have hf : (univ.filter fun c => a c < b c) =
      (univ.filter fun c => value c false ≠ value c true) := by
    ext c
    simp only [mem_filter,mem_univ,true_and]
    dsimp [a,b]
    omega
  rwa [hf] at hresult

theorem growing_window_aperture :
    ∀ᶠ X : ℝ in atTop,
      0 ≤ Sieve.growingReciprocalMarkerWindow X ∧
      Sieve.growingReciprocalMarkerWindow X ≤ X ∧
      (2*Sieve.growingReciprocalMarkerWindow X)^3 <
        27*(X-Sieve.growingReciprocalMarkerWindow X)^2 := by
  have hlim := Sieve.tendsto_log_growingReciprocalMarkerWindow_div_log_half
  filter_upwards [eventually_gt_atTop (27:ℝ),
    hlim.eventually (Iio_mem_nhds (by norm_num : (1:ℝ)/2 < 2/3))] with X hX hratio
  have hX0 : 0 < X := by linarith
  have hW : 0 < Sieve.growingReciprocalMarkerWindow X :=
    mul_pos (Real.sqrt_pos.mpr hX0) (Sieve.growingReciprocalMarkerH_pos X)
  have hlog : Real.log (Sieve.growingReciprocalMarkerWindow X) < (2/3:ℝ)*Real.log X :=
    (div_lt_iff₀ (Real.log_pos (by linarith))).mp hratio
  have hcube : (Sieve.growingReciprocalMarkerWindow X)^3 < X^2 := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow,Real.log_pow]
    norm_num
    linarith
  have hsmall : 3*Sieve.growingReciprocalMarkerWindow X < X := by
    by_contra hn
    have hc : X^3 ≤ (3*Sieve.growingReciprocalMarkerWindow X)^3 := by gcongr; linarith
    have hp : 0 < (X-27)*X^2 := mul_pos (by linarith) (by positivity)
    nlinarith
  have hmid : (2*X)^2 ≤ (3*(X-Sieve.growingReciprocalMarkerWindow X))^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  refine ⟨hW.le, by linarith, ?_⟩
  nlinarith [sq_nonneg X]

/-- The source-predeclared growing marker window eventually excludes three changing axes. -/
theorem eventually_complete_histogram_integer_components_at_most_two :
    ∀ᶠ X : ℝ in atTop, ∀ (n M : ℕ) (value : Fin n → Bool → ℕ),
      (∀ c b, 1 ≤ value c b) →
      (∀ h ∈ routeEComponentHistogramCell (fun _ : Fin n => Bool) (M+2)
          (routeEComponentHistoryLabel (fun _ : Fin n => Bool) (routeEPrimeActivationSeed n M)),
        ∀ r, routeEComponentSlotReceiver (fun _ : Fin n => Bool) (fun c b => (value c b:ℝ))
          h r ∈ Set.Icc (X-Sieve.growingReciprocalMarkerWindow X)
            (X+Sieve.growingReciprocalMarkerWindow X)) →
      (univ.filter fun c => value c false ≠ value c true).card ≤ 2 := by
  filter_upwards [growing_window_aperture] with X hX
  intro n M value hvalue haperture
  exact complete_histogram_integer_components_at_most_two n M value X
    (Sieve.growingReciprocalMarkerWindow X) hvalue hX.1 hX.2.1 hX.2.2 haperture

end RHTower.IntegerCubeAperture
