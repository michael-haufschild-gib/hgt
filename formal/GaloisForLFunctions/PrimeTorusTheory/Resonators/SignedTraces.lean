import GaloisForLFunctions.PrimeTorusTheory.Resonators.TheUnitCrossingsOfThreePrimePhases

/-!
# The quarter of the sign choices inside the unit disk

El Kaouni's three-phase trace factorization also controls the four
possible sign choices modulo a common change of sign. The product of
their four defects is minus a squared determinant product. Their pair
sums are nonnegative, so exactly one trace lies in the open unit disk
when all three directions are distinct modulo sign.
-/

noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.PrimeTorusTheory.ThreePhase

/-- Signed excess of the squared radius over the unit circle. -/
def unitDefect (a b c : ℂ) : ℝ := ‖a+b+c‖^2-1

/-- The oriented area of a pair of phase vectors (with the second conjugated). -/
def area (a b : ℂ) : ℝ := (a*conj b).im

private theorem unit_mul_conj {a : ℂ} (ha : ‖a‖=1) : a*conj a=1 := by
  rw [Complex.mul_conj',ha,one_pow,Complex.ofReal_one]

private theorem square_diff_area {a b : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) :
    a^2-b^2=(2*I*(area a b:ℂ))*(a*b) := by
  have h := Complex.sub_conj (a*conj b)
  simp only [map_mul,Complex.conj_conj,Complex.ofReal_mul,Complex.ofReal_ofNat] at h
  calc a^2-b^2 = a^2*(b*conj b)-b^2*(a*conj a) := by rw [unit_mul_conj ha,unit_mul_conj hb]; ring
       _ = ((a*conj b)-(conj a*b))*(a*b) := by ring
       _ = _ := by rw [h]; unfold area; ring

/-- A parallel pair of unit vectors is exactly an equal or antipodal pair. -/
theorem area_zero_iff {a b : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) :
    area a b=0 ↔ a=b ∨ a= -b := by
  have hz (z : ℂ) (h : ‖z‖=1) : z ≠ 0 := norm_ne_zero_iff.mp (h.trans_ne one_ne_zero)
  have hdiff := square_diff_area ha hb
  have hprod : a^2-b^2=(a-b)*(a+b) := by ring
  have he : a^2-b^2=0 ↔ area a b=0 := by
    rw [hdiff]
    simp [hz _ ha,hz _ hb]
  rw [← he,hprod,mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]

/-- The four defects have a nonpositive product with explicit magnitude. -/
theorem signed_defect_product {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    unitDefect a b c * unitDefect a b (-c) * unitDefect a (-b) c * unitDefect a (-b) (-c) =
      -64*(area a b*area a c*area b c)^2 := by
  let P := a*b*c
  have hP : P ≠ 0 := by
    have hnorm : ‖P‖=1 := by simp only [P,norm_mul,ha,hb,hc,mul_one]
    exact norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero)
  let D (u v : ℂ) : ℂ := (unitDefect a u v:ℂ)
  have h₀ : D b c * P = (a+b)*(a+c)*(b+c) := unit_trace_factor ha hb hc
  have h₁ : D b (-c) * P = -(a+b)*(a-c)*(b-c) := by
    have h := unit_trace_factor ha hb (show ‖-c‖=1 by rwa [norm_neg])
    change D b (-c) * (a*b*(-c)) = _ at h
    dsimp only [P]; linear_combination -h
  have h₂ : D (-b) c * P = -(a-b)*(a+c)*(c-b) := by
    have h := unit_trace_factor ha (show ‖-b‖=1 by rwa [norm_neg]) hc
    change D (-b) c * (a*(-b)*c) = _ at h
    dsimp only [P]; linear_combination -h
  have h₃ : D (-b) (-c) * P = -(a-b)*(a-c)*(b+c) := by
    have h := unit_trace_factor ha (show ‖-b‖=1 by rwa [norm_neg]) (show ‖-c‖=1 by rwa [norm_neg])
    change D (-b) (-c) * (a*(-b)*(-c)) = _ at h
    dsimp only [P]; linear_combination h
  have hpair (x y : ℂ) : (x+y)*(x-y)=x^2-y^2 := by ring
  have hd : D b c*D b (-c)*D (-b) c*D (-b) (-c)*P^4 =
      ((a^2-b^2)*(a^2-c^2)*(b^2-c^2))^2 := by
    rw [show D b c*D b (-c)*D (-b) c*D (-b) (-c)*P^4 =
      (D b c*P)*(D b (-c)*P)*(D (-b) c*P)*(D (-b) (-c)*P) by ring,h₀,h₁,h₂,h₃]
    rw [← hpair a b,← hpair a c,← hpair b c]
    ring
  apply Complex.ofReal_injective
  push_cast
  change D b c*D b (-c)*D (-b) c*D (-b) (-c) = _
  apply mul_right_cancel₀ (pow_ne_zero 4 hP)
  rw [hd,square_diff_area ha hb,square_diff_area ha hc,square_diff_area hb hc]
  have hi : I^6=(-1:ℂ) := by rw [show (6:ℕ)=2*3 by decide,pow_mul,Complex.I_sq]; norm_num
  dsimp only [P]
  linear_combination 64*(a*b*c)^4*((area a b:ℂ)*(area a c:ℂ)*(area b c:ℂ))^2*hi

private theorem opposite_sum (A B : ℂ) (hB : ‖B‖=1) :
    (‖A+B‖^2-1) + (‖A-B‖^2-1) = 2*‖A‖^2 := by
  have h : ‖A+B‖^2+‖A-B‖^2=2*(‖A‖^2+‖B‖^2) := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.sub_re,
      Complex.add_im,Complex.sub_im]
    ring
  rw [hB,one_pow] at h
  linarith only [h]

private def quartet (a b c : ℂ) : Fin 4 → ℝ :=
  ![unitDefect a b c,unitDefect a b (-c),unitDefect a (-b) c,unitDefect a (-b) (-c)]

private theorem pair_nonneg {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    {i j : Fin 4} (hij : i ≠ j) : 0 ≤ quartet a b c i+quartet a b c j := by
  have hp (x y A B : ℂ) (hB : ‖B‖=1) (hx : x=A+B ∨ x= -(A+B))
      (hy : y=A-B ∨ y= -(A-B)) : 0 ≤ (‖x‖^2-1)+(‖y‖^2-1) := by
    have hh := opposite_sum A B hB
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
      simp only [norm_neg,hh] <;> positivity
  have p01 := hp (a+b+c) (a+b+-c) (a+b) c hc (Or.inl rfl) (Or.inl (by ring))
  have p02 := hp (a+b+c) (a+-b+c) (a+c) b hb (Or.inl (by ring)) (Or.inl (by ring))
  have p03 := hp (a+b+c) (a+-b+-c) (b+c) a ha (Or.inl (by ring)) (Or.inr (by ring))
  have p12 := hp (a+b+-c) (a+-b+c) (b-c) a ha (Or.inl (by ring)) (Or.inr (by ring))
  have p13 := hp (a+b+-c) (a+-b+-c) (a-c) b hb (Or.inl (by ring)) (Or.inl (by ring))
  have p23 := hp (a+-b+c) (a+-b+-c) (a-b) c hc (Or.inl (by ring)) (Or.inl (by ring))
  fin_cases i <;> fin_cases j <;> first | exact False.elim (hij rfl) |
    (change 0 ≤ (‖_‖^2-1)+(‖_‖^2-1); first | assumption | (rw [add_comm]; assumption))

/-- Exactly one of the four traces up to common sign is strictly inside
the unit disk, for every triple without a parallel pair. -/
theorem exactly_one_subunit {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    (hab : area a b ≠ 0) (hac : area a c ≠ 0) (hbc : area b c ≠ 0) :
    ∃! j : Fin 4, (![‖a+b+c‖,‖a+b-c‖,‖a-b+c‖,‖a-b-c‖] : Fin 4 → ℝ) j < 1 := by
  let Q := quartet a b c
  have hprod : Q 0*Q 1*Q 2*Q 3 < 0 := by
    change unitDefect a b c * unitDefect a b (-c) * unitDefect a (-b) c * unitDefect a (-b) (-c) < 0
    rw [signed_defect_product ha hb hc]
    exact mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero hab hac) hbc))
  have hex : ∃ j, Q j < 0 := by
    by_contra! h
    exact hprod.not_ge (mul_nonneg (mul_nonneg (mul_nonneg (h 0) (h 1)) (h 2)) (h 3))
  have iffQ (i : Fin 4) : (![‖a+b+c‖,‖a+b-c‖,‖a-b+c‖,‖a-b-c‖] : Fin 4 → ℝ) i < 1 ↔ Q i < 0 := by
    have hh (z : ℂ) : ‖z‖<1 ↔ ‖z‖^2-1<0 := by
      constructor <;> intro hz <;> nlinarith only [hz,norm_nonneg z,sq_nonneg (‖z‖-1)]
    fin_cases i <;> simp [Q,quartet,unitDefect,← hh,sub_eq_add_neg]
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,(iffQ j).mpr hj,fun k hk => ?_⟩
  by_contra hne
  exact (add_neg ((iffQ k).mp hk) hj).not_ge (pair_nonneg ha hb hc hne)

/-- Four radii obtained by changing the two relative signs. -/
def signedRadii (a b c : ℂ) : Fin 4 → ℝ :=
  ![‖a+b+c‖,‖a+b-c‖,‖a-b+c‖,‖a-b-c‖]

/-- Outside parallel pairs, equal weighting of all relative signs puts
exactly one quarter of the mass in the open unit disk. -/
theorem sign_probability {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    (hab : area a b ≠ 0) (hac : area a c ≠ 0) (hbc : area b c ≠ 0) :
    (∑ j : Fin 4, if signedRadii a b c j < 1 then (1:ℝ) else 0)/4=1/4 := by
  obtain ⟨j,hj,hu⟩ := exactly_one_subunit ha hb hc hab hac hbc
  have hiff (k : Fin 4) : signedRadii a b c k < 1 ↔ k=j :=
    ⟨hu k,fun hk => hk ▸ hj⟩
  simp only [hiff,Finset.sum_ite_eq',Finset.mem_univ,if_true]

open Filter MeasureTheory

private theorem area_phase (p q : ℕ) (t : ℝ) :
    area (nPhase p t) (nPhase q t) = Real.sin ((Real.log p-Real.log q)*t) := by
  rw [area,conj_nPhase,nPhase,← Complex.exp_add]
  have he : I*((Real.log p:ℂ)*(t:ℂ))+I*((-(Real.log q):ℂ)*(t:ℂ)) =
      (((Real.log p-Real.log q)*t:ℝ):ℂ)*I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I_im]

private theorem ae_nonparallel {p q : ℕ} (hp : 0<p) (hpq : p<q) :
    ∀ᵐ t : ℝ, area (nPhase p t) (nPhase q t) ≠ 0 := by
  let w := Real.log p-Real.log q
  have hw : w≠0 := (sub_neg.mpr (Real.log_lt_log (Nat.cast_pos.mpr hp) (Nat.cast_lt.mpr hpq))).ne
  have hs : {t | area (nPhase p t) (nPhase q t)=0} ⊆ Set.range (fun k : ℤ => k*Real.pi/w) := by
    intro t ht
    obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp ((area_phase p q t) ▸ ht)
    exact ⟨k,(div_eq_iff hw).mpr (by dsimp only [w]; linarith only [hk])⟩
  rw [ae_iff]
  simpa only [not_ne_iff] using ((Set.countable_range _).mono hs).measure_zero volume

/-- On every finite time interval, averaging the four signed resonators
gives exactly one quarter of the interval inside the unit disk. Distinct
integer frequencies suffice, even when their logarithms are dependent. -/
theorem finite_time_quarter {p q r : ℕ} (hp : 0<p) (hpq : p<q) (hqr : q<r) (A B : ℝ) :
    (∫ t in A..B, (∑ j : Fin 4, if signedRadii (nPhase p t) (nPhase q t) (nPhase r t) j < 1
      then (1:ℝ) else 0)/4) = (B-A)/4 := by
  have he : ∀ᵐ t : ℝ, (∑ j : Fin 4, if signedRadii (nPhase p t) (nPhase q t) (nPhase r t) j < 1
      then (1:ℝ) else 0)/4 = 1/4 := by
    filter_upwards [ae_nonparallel hp hpq,ae_nonparallel hp (hpq.trans hqr),
      ae_nonparallel (hp.trans hpq) hqr] with t h₁ h₂ h₃
    exact sign_probability (norm_nPhase _ _) (norm_nPhase _ _) (norm_nPhase _ _) h₁ h₂ h₃
  calc _ = ∫ _t in A..B, (1/4:ℝ) := intervalIntegral.integral_congr_ae (he.mono fun _ h _ => h)
       _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]; ring

end GaloisForLFunctions.PrimeTorusTheory.ThreePhase
