import GaloisForLFunctions.RestrictedFactorizationCalculus.SmoothCofactorsInEveryQuotientInterval
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothPopulationInASignedRoughPrefix

/-!
# The logarithmic threshold for signed rough prefixes

At a polynomial prime cutoff the smooth population at the quotient
endpoint forces negative charge of order X/log X. As long as both the
cutoff and its quotient grow, the charge is o(X/log X) exactly at
subpolynomial cutoffs.
-/

noncomputable section

open Finset Filter RHTower.Sieve GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem lower_smooth_fraction (j : ℕ) : ∃ c : ℝ,0<c ∧ ∃ Z : ℕ,4 ≤ Z ∧
    ∀ y X : ℕ,Z ≤ y → Z*y ≤ X → X ≤ y^j →
      c*X ≤ (y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card := by
  obtain ⟨b,hb,eventual⟩ := positive_smooth_population_at_all_polynomial_walls (3*j)
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventual
  let V := max 8 N
  let Z := 2*(V+1)^2
  have eight := le_max_left 8 N
  have many : 4 ≤ Z := by dsimp only [Z,V]; nlinarith only [eight,sq_nonneg (max 8 N : ℕ)]
  refine ⟨b/6,by positivity,Z,many,?_⟩
  intro y X zy high cut
  let s := Nat.sqrt (y/2)
  let T := X/y
  let u := T/2
  have ypos : 0<y := by omega
  have large : V+1 ≤ s := Nat.le_sqrt.mpr (by
    rw [←pow_two,Nat.le_div_iff_mul_le (by decide : 0<2),mul_comm]; exact zy)
  have s8 : 8 ≤ s := by change 8 ≤ V at eight; omega
  have sq : 2*s^2 ≤ y := (Nat.mul_le_mul_left 2 (Nat.sqrt_le' (y/2))).trans (Nat.mul_div_le y 2)
  have sq' : y/2<(s+1)^2 := by
    by_contra! no
    exact (Nat.not_succ_le_self s) (Nat.le_sqrt.mpr (by simpa only [pow_two] using no))
  have cubic : y ≤ s^3 := by
    have estimate : 2*(s+1)^2 ≤ s^3 := by
      have sqle := Nat.pow_le_pow_left (by omega : s+1 ≤ 2*s) 2
      calc 2*(s+1)^2 ≤ 2*(2*s)^2 := Nat.mul_le_mul_left _ sqle
           _ = 8*s^2 := by ring
           _ ≤ s*s^2 := Nat.mul_le_mul_right _ s8
           _ = s^3 := by ring
    omega
  have uy : u ≤ s^(3*j) := ((Nat.div_le_self T 2).trans ((Nat.div_le_self X y).trans cut)).trans
    ((Nat.pow_le_pow_left cubic j).trans_eq (pow_mul ..).symm)
  have inputs := hN s ((le_max_right 8 N).trans large.le) u uy
  let S := smoothUpTo (Nat.primesLE y) T
  have sub : smoothQuotientInterval (2*s^2) u ⊆ S := by
    intro n hn
    obtain ⟨hi,smooth⟩ := mem_filter.mp hn
    obtain ⟨lo,up⟩ := mem_Ioc.mp hi
    apply mem_smoothUpTo.mpr
    refine ⟨⟨Nat.zero_lt_of_lt lo,up.trans (Nat.mul_div_le T 2)⟩,?_⟩
    intro p hp
    obtain ⟨pmax,pr⟩ := Nat.mem_primesLE.mp (smooth hp)
    exact Nat.mem_primesLE.mpr ⟨pmax.trans sq,pr⟩
  have measured := inputs.trans (Nat.cast_le.mpr (card_le_card sub))
  have tlarge : Z ≤ T := (Nat.le_div_iff_mul_le ypos).mpr high
  have triple : T ≤ 3*u := by dsimp only [u]; omega
  have xupper : X ≤ 2*(y*T) := by
    have rem := Nat.mod_add_div X y
    have small := Nat.mod_lt X ypos
    have pos := Nat.mul_le_mul_left y (show 1 ≤ T by omega)
    change X%y+y*T=X at rem
    omega
  have charge : (X:ℝ) ≤ 6*((y:ℝ)*u) := by
    exact_mod_cast (xupper.trans ((Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left y triple)).trans_eq (by ring)))
  have weighted := mul_le_mul_of_nonneg_left measured (Nat.cast_nonneg y)
  linarith only [weighted,mul_le_mul_of_nonneg_left charge hb.le]

/-- A single negative lower bound at every polynomially rough cutoff,
uniform over both integers once y and X/y are sufficiently large. -/
theorem negative_charge_of_every_polynomial_rough_cutoff (j : ℕ) :
    ∃ c : ℝ,0<c ∧ ∃ Z : ℕ,0<Z ∧ ∀ y X : ℕ,Z ≤ y → Z*y ≤ X → X ≤ y^j →
      Real.log X*coprimeMoebiusSum (primorial y) X ≤ -(c*X) := by
  obtain ⟨a,ha,L,hL,pop⟩ := lower_smooth_fraction j
  obtain ⟨U,hU,transfer⟩ := signed_rough_prefix_tracks_smooth_population (half_pos ha)
  refine ⟨a/2,half_pos ha,max L U,hU.trans_le (le_max_right ..),?_⟩
  intro y X hy hx cut
  have b := pop y X ((le_max_left ..).trans hy) ((Nat.mul_le_mul_right _ (le_max_left ..)).trans hx) cut
  have s := (abs_le.mp (transfer y X ((le_max_right ..).trans hy)
    ((Nat.mul_le_mul_right _ (le_max_right ..)).trans hx))).2
  linarith only [s,b]

/-- For a frozen prime cutoff y(X), the ordinary rough prefix has
o(X/log X) charge exactly when every fixed power of y(X) is eventually
smaller than X. The cutoff and the quotient must both tend to infinity. -/
theorem subpolynomial_cutoff_iff_logarithmic_signed_saving (y : ℕ → ℕ)
    (grows : Tendsto y atTop atTop) (quotient : Tendsto (fun X => X/y X) atTop atTop) :
    (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
      |Real.log X*coprimeMoebiusSum (primorial (y X)) X| ≤ ε*X) ↔
    ∀ j : ℕ,∀ᶠ X : ℕ in atTop,y X^j<X := by
  constructor
  · intro saved j
    obtain ⟨c,hc,Z,hZ,negative⟩ := negative_charge_of_every_polynomial_rough_cutoff j
    filter_upwards [saved (c/2) (half_pos hc),grows.eventually_ge_atTop Z,
      quotient.eventually_ge_atTop Z,eventually_ge_atTop (1:ℕ)] with X charge hy hq hx
    by_contra! large
    have yp := hZ.trans_le hy
    have down := negative _ X hy ((Nat.le_div_iff_mul_le yp).mp hq) large
    have loss := (abs_le.mp charge).1
    have positive := mul_pos hc (Nat.cast_pos.mpr hx : (0:ℝ)<X)
    linarith only [loss,down,positive]
  · intro small ε hε
    obtain ⟨K,hK,upper⟩ := uniform_logarithmic_upper_bound_for_smooth_population
    obtain ⟨Z,hZ,transfer⟩ := signed_rough_prefix_tracks_smooth_population (half_pos hε)
    let j := ⌈4/ε⌉₊+1
    have jpos : 0<j := Nat.succ_pos _
    have ratio : 4 ≤ (j:ℝ)*ε := (div_le_iff₀ hε).mp ((Nat.le_ceil _).trans
      (Nat.cast_le.mpr (Nat.le_succ _)))
    have logY := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp grows)
    filter_upwards [small (j+1),grows.eventually_ge_atTop (max Z 2),quotient.eventually_ge_atTop Z,
      logY.eventually_ge_atTop K] with X cut hy hq large
    let p := y X
    let T := X/p
    have yp := hZ.trans_le ((le_max_left ..).trans hy)
    have two : 2 ≤ p := (le_max_right ..).trans hy
    have lp : 0<Real.log p := Real.log_pos (by exact_mod_cast (show 1<p by omega))
    have before : p^j ≤ T := (Nat.le_div_iff_mul_le yp).mpr (by simpa only [pow_succ] using cut.le)
    have lg := Real.log_le_log (by exact_mod_cast Nat.pow_pos yp j)
      ((Nat.cast_le (α := ℝ)).mpr before)
    rw [Nat.cast_pow,Real.log_pow] at lg
    have top := upper p T yp
    have quot : (p:ℝ)*(T:ℝ) ≤ X := by exact_mod_cast Nat.mul_div_le X p
    let S := (smoothUpTo (Nat.primesLE p) T).card
    have paid : (p:ℝ)*S ≤ ε/2*X := by
      have bound : (j:ℝ)*Real.log p*S ≤ (T:ℝ)*(2*Real.log p) :=
        (mul_le_mul_of_nonneg_right lg (Nat.cast_nonneg S)).trans
          ((mul_comm ..).trans_le (top.trans (mul_le_mul_of_nonneg_left
            (by linarith only [large] : Real.log p+K ≤ 2*Real.log p) (Nat.cast_nonneg T))))
      have h : (j:ℝ)*S ≤ 2*T := (mul_le_mul_iff_left₀ lp).mp (by linarith only [bound])
      have scale := mul_le_mul_of_nonneg_right ratio (Nat.cast_nonneg (α := ℝ) S)
      have limit := mul_le_mul_of_nonneg_left h hε.le
      have s : (S:ℝ) ≤ ε/2*T := by linarith only [scale,limit]
      have w := mul_le_mul_of_nonneg_left s (Nat.cast_nonneg p)
      linarith only [w,mul_le_mul_of_nonneg_left quot (half_pos hε).le]
    have approx := abs_le.mp (transfer p X ((le_max_left ..).trans hy) ((Nat.le_div_iff_mul_le yp).mp hq))
    change -_ ≤ _+(p:ℝ)*S ∧ _+(p:ℝ)*S ≤ _ at approx
    rw [abs_le]
    have pos := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (Nat.cast_nonneg (α := ℝ) S)
    have xpos := mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) X)
    constructor <;> linarith only [approx.1,approx.2,paid,pos,xpos]

#print axioms negative_charge_of_every_polynomial_rough_cutoff
#print axioms subpolynomial_cutoff_iff_logarithmic_signed_saving

end GaloisForLFunctions.RestrictedFactorizationCalculus
