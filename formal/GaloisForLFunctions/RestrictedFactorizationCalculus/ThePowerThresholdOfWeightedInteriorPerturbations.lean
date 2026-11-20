import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeOnlyQuotientRowsOfTheRoughInterior

/-!
# The power threshold for weighted interior perturbations

A weighted ℓ¹ budget allows a perturbation concentrated at one site.
The last site passes at full strength, forcing its weight exponent.
The first site samples the entire rough Möbius prefix up to a removable
small head, forcing the zero abscissa. Finite Euler deletion gives the
matching upper bound at every intermediate site and every head.
-/
noncomputable section
open Filter Finset ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Topology Classical ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev F (y t : ℕ) := coprimeMoebiusSum (primorial y) t
private abbrev wall := logSquareCutoff
private abbrev cut (X : ℕ) := ⌊(X:ℝ)^(4/7:ℝ)⌋₊

/-- A uniform power bound on all independently selectable quotient sites
at the specified observation head, priced by the weight q^s. -/
def weightedInteriorPower (s β : ℝ) (T : ℕ → ℕ) :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ q ∈ Icc 1 X,
    (q : ℝ)^s * |interiorKernel (logSquareCutoff X) X (T X) q| ≤ C * (X : ℝ)^β

/-- The frozen wall has a uniform Euler-product price at every exponent above the zero abscissa. -/
theorem rough_prefix_above_the_zero_abscissa {u : ℝ} (hu : _root_.RHTower.zetaZeroAbscissa < u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y t : ℕ, |F y t| ≤ C*deletionPrice u y*(t:ℝ)^u := by
  have up : 0 < u := (by norm_num : (0:ℝ) < 1/2).trans (_root_.RHTower.half_le_zetaZeroAbscissa.trans_lt hu)
  obtain ⟨B,hB,full⟩ := exists_moebius_power_bound_of_abscissa_lt hu
  have alln (n : ℕ) : |coprimeMoebiusSum 1 n| ≤ B*(n:ℝ)^u := by
    rcases Nat.eq_zero_or_pos n with rfl|hn
    · simp [coprimeMoebiusSum,Real.zero_rpow up.ne']
    simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using full n hn
  exact ⟨2*B,by positivity,fun y t => all_frozen_rows_from_full_prefix up hB alln t y⟩

private theorem cheap_square {s η : ℝ} (hs : 1/2 < s) (he : 0 < η) :
    ∀ᶠ X : ℕ in atTop, (deletionPrice s (wall X))^2 ≤ (X:ℝ)^η := by
  filter_upwards [log_square_deletion_cost hs he] with X hx
  have factor : 1 ≤ (wall X : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact (le_mul_of_one_le_left (sq_nonneg _) factor).trans hx

private theorem cheap_price {s η : ℝ} (hs : 1/2 < s) (he : 0 < η) :
    ∀ᶠ X : ℕ in atTop, deletionPrice s (wall X) ≤ (X:ℝ)^η := by
  filter_upwards [cheap_square hs he] with X hx
  have h := deletionPrice_one_le ((by norm_num : (0:ℝ) < 1/2).trans hs) (wall X)
  exact (show deletionPrice s (wall X) ≤ (deletionPrice s (wall X))^2 by nlinarith only [h,sq_nonneg (deletionPrice s (wall X)-1)]).trans hx

/-- Constant-weight inversion at a single monotone sequence of frozen
walls reads the full zero abscissa whenever its Euler price is subpolynomial. -/
theorem abscissa_from_frozen_rows {β : ℝ} (hb : 1/2 ≤ β) (b : ℕ → ℕ) (mono : Monotone b)
    (prices : ∀ s : ℝ, 1/2 < s → ∀ η : ℝ, 0 < η →
      ∀ᶠ X : ℕ in atTop, (deletionPrice s (b X))^2 ≤ (X:ℝ)^η)
    (rows : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ X : ℕ in atTop, |F (b X) X| ≤ C*(X:ℝ)^(β+η)) :
    _root_.RHTower.zetaZeroAbscissa ≤ β := by
  by_contra! bad
  let η := (_root_.RHTower.zetaZeroAbscissa-β)/3
  let s := β+η
  have hη : 0 < η := div_pos (sub_pos.mpr bad) (by norm_num)
  have hs : 1/2 < s := hb.trans_lt (lt_add_of_pos_right β hη)
  have hp := (by norm_num : (0:ℝ) < 1/2).trans hs
  obtain ⟨C,hC⟩ := rows η hη
  have h0 : (fun X => F (b X) X) 0=0 := by simp [coprimeMoebiusSum]
  obtain ⟨B,hB,alln⟩ := prefixPower_of_eventual (f := fun n => F (b n) n) h0 hp hC
  have restore (X : ℕ) : |coprimeMoebiusSum 1 X| ≤ B*(deletionPrice s (b X))^2*(X:ℝ)^s := by
    refine full_prefix_from_one_weighted_reading b mono (fun _ => 1) (fun _ _ _ => le_rfl) zero_lt_one hp hB ?_ X
    intro n
    simpa only [weightedFrozenPrefix,mul_one,coprimeMoebiusSum] using alln n
  have upper : ∀ᶠ n : ℕ in atTop, |coprimeMoebiusSum 1 n| ≤ B*(n:ℝ)^(s+η) := by
    filter_upwards [prices s hs η hη,eventually_ge_atTop 1] with n hn np
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hB) (Real.rpow_nonneg (Nat.cast_nonneg n) s)
    rw [Real.rpow_add (Nat.cast_pos.mpr np)]
    exact (restore n).trans (he.trans_eq (by ring))
  obtain ⟨A,hA,hall⟩ := prefixPower_of_eventual (f := coprimeMoebiusSum 1)
    (by simp [coprimeMoebiusSum]) (add_pos hp hη) upper
  have hh := zetaZeroAbscissa_le_of_moebius_power_bound hA (add_pos hp hη).le
    (fun n _ => by simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using hall n)
  dsimp only [s,η] at hh
  linarith only [hh,bad]

/-- Every head, including heads beyond the observation, obeys the upper
power price as soon as both endpoint exponents are covered. -/
theorem upper_weighted_sites_all_heads {s β : ℝ} (hs : s ≤ β)
    (strip : _root_.RHTower.zetaZeroAbscissa ≤ β) {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ T : ℕ, ∀ q ∈ Icc 1 X,
      (q:ℝ)^s*|interiorKernel (wall X) X T q| ≤ C*(X:ℝ)^(β+ε) := by
  let u := β+ε/2
  have su : s ≤ u := hs.trans (le_add_of_nonneg_right (half_pos he).le)
  have hu := strip.trans_lt (lt_add_of_pos_right β (half_pos he))
  have hu' : 1/2 < u := _root_.RHTower.half_le_zetaZeroAbscissa.trans_lt hu
  have up := (by norm_num : (0:ℝ) < 1/2).trans hu'
  obtain ⟨B,hB,rows⟩ := rough_prefix_above_the_zero_abscissa hu
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [cheap_price hu' (half_pos he),eventually_ge_atTop 1] with X cheap xp
  intro T q hq
  let y := wall X
  have qp := (mem_Icc.mp hq).1
  have qr : 0 < (q:ℝ) := Nat.cast_pos.mpr qp
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast qp
  have x0 := (Nat.cast_pos (α:=ℝ)).mpr xp
  have factor := Real.rpow_nonneg qr.le s
  have D0 := zero_le_one.trans (deletionPrice_one_le up y)
  have bound (t : ℕ) (ht : t ≤ X) : (q:ℝ)^s*|F y (t/q)| ≤ B*(X:ℝ)^(β+ε) := by
    have floor : ((t/q:ℕ):ℝ) ≤ (X:ℝ)/q := (le_div_iff₀ qr).mpr (by exact_mod_cast (Nat.div_mul_le_self t q).trans ht)
    have row := (rows y _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) floor up.le) (mul_nonneg hB D0))
    have hqpow := Real.rpow_le_rpow_of_exponent_le q1 su
    apply (mul_le_mul hqpow row (abs_nonneg _) (Real.rpow_nonneg qr.le u)).trans
    rw [Real.div_rpow x0.le qr.le,show (q:ℝ)^u*(B*deletionPrice u y*((X:ℝ)^u/(q:ℝ)^u))=
      B*deletionPrice u y*(X:ℝ)^u by field_simp [(Real.rpow_pos_of_pos qr u).ne']]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cheap hB) (Real.rpow_nonneg x0.le _)).trans_eq
    rw [mul_assoc,←Real.rpow_add x0,show ε/2+u=β+ε by dsimp only [u]; ring]
  have htri := mul_le_mul_of_nonneg_left (abs_sub (F y (X/q)) (F y (min X T/q))) factor
  rw [mul_add] at htri
  apply htri.trans ((add_le_add (bound X le_rfl) (bound _ (min_le_left X T))).trans_eq ?_)
  ring

private theorem head_power {α u η : ℝ} (T : ℕ → ℕ)
    (room : ∀ᶠ X : ℕ in atTop, (T X:ℝ) ≤ (X:ℝ)^α)
    (hu : _root_.RHTower.zetaZeroAbscissa < u) (hη : 0 < η) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ᶠ X : ℕ in atTop,
      |F (wall X) (min X (T X))| ≤ D*(X:ℝ)^(α*u+η) := by
  have half := _root_.RHTower.half_le_zetaZeroAbscissa.trans_lt hu
  have up := (by norm_num : (0:ℝ)<1/2).trans half
  obtain ⟨D,hD,rows⟩ := rough_prefix_above_the_zero_abscissa hu
  refine ⟨D,hD,?_⟩
  filter_upwards [room,cheap_price half hη,eventually_ge_atTop (1:ℕ)] with X top price xp
  have x0 : 0 < (X:ℝ) := Nat.cast_pos.mpr xp
  have bound := Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) (min X (T X)))
    ((Nat.cast_le.mpr (min_le_right X (T X))).trans top) up.le
  rw [←Real.rpow_mul x0.le] at bound
  have prod := mul_le_mul (mul_le_mul_of_nonneg_left price hD) bound
    (Real.rpow_nonneg (Nat.cast_nonneg _) u) (mul_nonneg hD (Real.rpow_nonneg x0.le η))
  apply (rows _ _).trans (prod.trans_eq ?_)
  rw [mul_assoc,←Real.rpow_add x0,add_comm η]

/-- A single quotient site detects the full zero abscissa for any head
bounded by a fixed power below one. A hypothetical excess of the abscissa
over β contracts strictly at the smaller endpoint. -/
theorem first_site_at_each_power_saving_head {β α : ℝ} (hb : 1/2 ≤ β) (ha : α < 1)
    (T : ℕ → ℕ) (room : ∀ᶠ X : ℕ in atTop, (T X:ℝ) ≤ (X:ℝ)^α) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ X : ℕ in atTop,
      |interiorKernel (wall X) X (T X) 1| ≤ C*(X:ℝ)^(β+ε)) ↔
        _root_.RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro measured
    by_contra! bad
    let θ := _root_.RHTower.zetaZeroAbscissa
    let η := min (θ-β) ((1-α)*θ)/4
    have θp : 0 < θ := (by norm_num : (0:ℝ)<1/2).trans_le _root_.RHTower.half_le_zetaZeroAbscissa
    have ηp : 0 < η := div_pos (lt_min (sub_pos.mpr bad) (mul_pos (sub_pos.mpr ha) θp)) (by norm_num)
    have left : 4*η ≤ θ-β := by
      dsimp only [η];linarith only [min_le_left (θ-β) ((1-α)*θ)]
    have right : 4*η ≤ (1-α)*θ := by
      dsimp only [η];linarith only [min_le_right (θ-β) ((1-α)*θ)]
    let γ := θ-η
    have βγ : β+η ≤ γ := by dsimp only [γ];linarith only [left,ηp]
    have αγ : α*(θ+η)+η ≤ γ := by
      dsimp only [γ];nlinarith only [right,ηp,mul_nonneg (sub_nonneg.mpr ha.le) ηp.le]
    obtain ⟨C,obs⟩ := measured η ηp
    obtain ⟨D,hD,pay⟩ := head_power T room (lt_add_of_pos_right θ ηp) ηp
    have strip := abscissa_from_frozen_rows (β:=γ) (hb.trans ((le_add_of_nonneg_right ηp.le).trans βγ))
      wall logSquareCutoff_mono (fun _ hs _ he => cheap_square hs he) (by
        intro ε he
        refine ⟨|C|+D,?_⟩
        filter_upwards [obs,pay,eventually_ge_atTop (1:ℕ)] with X signal head hx
        have x1 : 1 ≤ (X:ℝ) := Nat.one_le_cast.mpr hx
        have ge : γ ≤ γ+ε := le_add_of_nonneg_right he.le
        have h₁ := mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le x1 (βγ.trans ge))
          (Real.rpow_nonneg (Nat.cast_nonneg X) _) (abs_nonneg C)
        have h₂ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le x1 (αγ.trans ge)) hD
        have hsum := abs_add_le (interiorKernel (wall X) X (T X) 1) (F (wall X) (min X (T X)))
        have eq : interiorKernel (wall X) X (T X) 1+F (wall X) (min X (T X))=F (wall X) X := by
          simp only [interiorKernel,Nat.div_one,sub_add_cancel]
        rw [eq] at hsum
        exact hsum.trans ((add_le_add (signal.trans h₁) (head.trans h₂)).trans_eq (add_mul ..).symm))
    change θ ≤ θ-η at strip
    linarith only [strip,ηp]
  · intro h ε he
    obtain ⟨C,_,cap⟩ := upper_weighted_sites_all_heads (show (0:ℝ) ≤ β by linarith) h he
    refine ⟨C,?_⟩
    filter_upwards [cap,eventually_ge_atTop 1] with X hX xp
    simpa only [Nat.cast_one,Real.one_rpow,one_mul] using hX (T X) 1 (mem_Icc.mpr ⟨le_rfl,xp⟩)

private theorem cut_bound : ∀ᶠ X : ℕ in atTop, (cut X:ℝ) ≤ (X:ℝ)^(4/7:ℝ) :=
  .of_forall fun X => Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) _)

/-- At the four-sevenths head the first quotient site retains the entire abscissa test. -/
theorem first_quotient_site_detects_the_abscissa {β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ X : ℕ in atTop,
      |interiorKernel (wall X) X (cut X) 1| ≤ C*(X:ℝ)^(β+ε)) ↔
        _root_.RHTower.zetaZeroAbscissa ≤ β :=
  first_site_at_each_power_saving_head hb (by norm_num : (4/7:ℝ)<1) cut cut_bound

private theorem last_site_transmits {α : ℝ} (ha : α < 1) (T : ℕ → ℕ)
    (room : ∀ᶠ X : ℕ in atTop, (T X:ℝ) ≤ (X:ℝ)^α) :
    ∀ᶠ X : ℕ in atTop, interiorKernel (wall X) X (T X) X=1 := by
  filter_upwards [room,eventually_ge_atTop (2:ℕ),logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1]
    with X upper hx hy
  have h1 : (1:ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have ht : (X:ℝ)^α < X := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt h1 ha
  have hcut : T X < X := by exact_mod_cast upper.trans_lt ht
  apply interior_kernel_upper_plateau (by omega) le_rfl hcut
  simpa only [Nat.div_self (by omega : 0 < X)] using hy

/-- Above the square-root boundary the weighted site exponent is the
larger of the input exponent and the zeta zero abscissa at every head
with a fixed power saving. -/
theorem weighted_threshold_at_power_saving_heads {s β α : ℝ} (hb : 1/2 ≤ β) (ha : α < 1)
    (T : ℕ → ℕ) (room : ∀ᶠ X : ℕ in atTop, (T X:ℝ) ≤ (X:ℝ)^α) :
    (∀ ε : ℝ, 0 < ε → weightedInteriorPower s (β+ε) T) ↔
      max s _root_.RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro h
    apply max_le
    · by_contra! higher
      let η := (s-β)/2
      have he : 0 < η := half_pos (sub_pos.mpr higher)
      obtain ⟨C,_,upper⟩ := h η he
      have hg := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
      obtain ⟨X,cap,hlast,hgrow,hX⟩ := (upper.and ((last_site_transmits ha T room).and
        ((hg.eventually_gt_atTop C).and (eventually_ge_atTop 1)))).exists
      have hx := (Nat.cast_pos (α:=ℝ)).mpr hX
      have hi := cap X (mem_Icc.mpr ⟨hX,le_rfl⟩)
      rw [hlast,abs_one,mul_one,show s=η+(β+η) by dsimp only [η];ring,Real.rpow_add hx] at hi
      exact ((mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hx (β+η))).mp hi).not_gt hgrow
    · apply (first_site_at_each_power_saving_head hb ha T room).mp
      intro ε he
      obtain ⟨C,_,cap⟩ := h ε he
      refine ⟨C,?_⟩
      filter_upwards [cap,eventually_ge_atTop 1] with X hX hx
      simpa only [Nat.cast_one,Real.one_rpow,one_mul] using hX 1 (mem_Icc.mpr ⟨le_rfl,hx⟩)
  · intro h ε he
    obtain ⟨C,hC,cap⟩ := upper_weighted_sites_all_heads ((le_max_left ..).trans h) ((le_max_right ..).trans h) he
    exact ⟨C,hC,cap.mono fun X hx => hx (T X)⟩

/-- The exact power threshold for weighted perturbations at the four-sevenths head. -/
theorem sharp_weighted_four_sevenths_threshold {s β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ, 0 < ε → weightedInteriorPower s (β+ε) cut) ↔
      max s _root_.RHTower.zetaZeroAbscissa ≤ β :=
  weighted_threshold_at_power_saving_heads hb (by norm_num : (4/7:ℝ)<1) cut cut_bound

/-- Uniform control of every removed head has the very same threshold. -/
theorem all_head_weighted_threshold {s β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ T : ℕ, ∀ q ∈ Icc 1 X,
      (q:ℝ)^s*|interiorKernel (wall X) X T q| ≤ C*(X:ℝ)^(β+ε)) ↔
      max s _root_.RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro h
    apply (sharp_weighted_four_sevenths_threshold hb).mp
    intro ε he
    obtain ⟨C,hC,cap⟩ := h ε he
    exact ⟨C,hC,cap.mono fun X hx => hx (cut X)⟩
  · exact fun h _ he => upper_weighted_sites_all_heads ((le_max_left ..).trans h) ((le_max_right ..).trans h) he

#print axioms first_site_at_each_power_saving_head
#print axioms weighted_threshold_at_power_saving_heads
#print axioms first_quotient_site_detects_the_abscissa
#print axioms sharp_weighted_four_sevenths_threshold
#print axioms all_head_weighted_threshold
end GaloisForLFunctions.RestrictedFactorizationCalculus
