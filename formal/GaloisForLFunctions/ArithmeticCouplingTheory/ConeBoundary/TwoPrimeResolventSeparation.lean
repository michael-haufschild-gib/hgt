import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.TwoClockResolvent
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TwoPrimeTowersSeeEveryOrdinateDifference
import GaloisForLFunctions.HTGeometry.CircleEmbeddingBiLipschitz

/-!
# Polynomial separation of the two-prime resolvent

Baker separation of two prime phases becomes a joint chord bound. The
real part of an averaged damped phase controls the squared chord defect.
Together with radial contraction, this bounds the exponential denominator
below by an inverse polynomial on the closed left half-plane outside any
fixed neighborhood of its simple zero.
-/

open Complex Real
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- A nearest phase lift is controlled by its unit-circle chord. -/
lemma exists_phase_alias_le_chord (θ : ℝ) :
    ∃ k : ℤ, |θ-2*Real.pi*k| ≤ Real.pi/2*‖Complex.exp ((θ:ℂ)*I)-1‖ := by
  let u := θ/(2*Real.pi)
  have he : 2*(Real.pi:ℂ)*(u:ℂ)*I=(θ:ℂ)*I := by
    dsimp only [u]
    push_cast
    field_simp [Real.pi_ne_zero]
  have h := (HTGeometry.norm_circleEmbed_sub_one_bounds (u:UnitAddCircle)).1
  rw [HTGeometry.circleEmbed_coe,UnitAddCircle.norm_eq,he] at h
  refine ⟨round u,?_⟩
  have he' : θ-2*Real.pi*(round u:ℤ)=2*Real.pi*(u-(round u:ℤ)) := by
    dsimp only [u]
    field_simp [Real.pi_ne_zero]
  rw [he',abs_mul,abs_of_pos (mul_pos zero_lt_two Real.pi_pos)]
  have hh := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  linarith only [hh]

/-- Distinct prime clocks have joint polynomial chord separation. -/
lemma exists_two_prime_chord_separation {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Δ : ℝ,
      c*min |Δ| ((2+|Δ|)^(-C)) ≤
        ‖Complex.exp (((Δ*Real.log p:ℝ):ℂ)*I)-1‖+
        ‖Complex.exp (((Δ*Real.log q:ℝ):ℂ)*I)-1‖ := by
  obtain ⟨c,C,hc,hC,hsep⟩ :=
    ArithmeticOfSquareRootPrecision.two_prime_alias_bound_in_Δ hp hq hpq
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  let K := Real.pi/2*(Real.log p+Real.log q)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨c/K,C,div_pos hc hK,hC,?_⟩
  intro Δ
  obtain ⟨k,hk⟩ := exists_phase_alias_le_chord (Δ*Real.log p)
  obtain ⟨l,hl⟩ := exists_phase_alias_le_chord (Δ*Real.log q)
  let A := ‖Complex.exp (((Δ*Real.log p:ℝ):ℂ)*I)-1‖
  let B := ‖Complex.exp (((Δ*Real.log q:ℝ):ℂ)*I)-1‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hphase := hsep Δ k l
  have hfirst := mul_le_mul_of_nonneg_right hk hb.le
  have hsecond := mul_le_mul_of_nonneg_right hl ha.le
  have hweights : Real.log q*A+Real.log p*B ≤ (Real.log p+Real.log q)*(A+B) := by
    nlinarith only [mul_nonneg ha.le hA,mul_nonneg hb.le hB]
  have hweights' := mul_le_mul_of_nonneg_left hweights (div_nonneg Real.pi_pos.le zero_le_two)
  have hbound : c*min |Δ| ((2+|Δ|)^(-C)) ≤ K*(A+B) := by
    dsimp only [K]
    change |Δ*Real.log p-2*Real.pi*k| *Real.log q ≤ (Real.pi/2*A)*Real.log q at hfirst
    change |Δ*Real.log q-2*Real.pi*l| *Real.log p ≤ (Real.pi/2*B)*Real.log p at hsecond
    nlinarith only [hphase,hfirst,hsecond,hweights']
  change c/K*min |Δ| ((2+|Δ|)^(-C)) ≤ A+B
  rw [div_mul_eq_mul_div,div_le_iff₀ hK]
  simpa only [mul_comm] using hbound

lemma unit_chord_sq {u : ℂ} (hu : ‖u‖=1) : ‖1-u‖^2=2*(1-u.re) := by
  have hh := Complex.normSq_eq_norm_sq u
  rw [hu,one_pow,Complex.normSq_apply] at hh
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im]
  nlinarith only [hh]

/-- Averaging damped unit phases retains a positive quadratic chord defect. -/
lemma averaged_chord_defect_lower {u v : ℂ} (hu : ‖u‖=1) (hv : ‖v‖=1)
    {r t η : ℝ} (hr : r ≤ 1) (ht : t ≤ 1) (hηr : η ≤ r) (hηt : η ≤ t) :
    η/4*(‖1-u‖^2+‖1-v‖^2) ≤ (1-((r:ℂ)*u+(t:ℂ)*v)/2).re := by
  have hur : u.re ≤ 1 := by simpa only [hu] using Complex.re_le_norm u
  have hvr : v.re ≤ 1 := by simpa only [hv] using Complex.re_le_norm v
  rw [unit_chord_sq hu,unit_chord_sq hv]
  simp only [Complex.sub_re,Complex.one_re,Complex.div_ofNat_re,Complex.add_re,
    Complex.re_ofReal_mul]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hηr) (sub_nonneg.mpr hur),
    mul_nonneg (sub_nonneg.mpr hηt) (sub_nonneg.mpr hvr),hr,ht]

lemma clockDefect_radial_lower (a b : ℝ) (w : ℂ) :
    1-(Real.exp (a*w.re)+Real.exp (b*w.re))/2 ≤ ‖clockDefect a b w‖ := by
  have htri := norm_add_le (Complex.exp ((a:ℂ)*w)) (Complex.exp ((b:ℂ)*w))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.re_ofReal_mul,Complex.re_ofReal_mul] at htri
  have hrev := norm_sub_norm_le (1:ℂ)
    ((Complex.exp ((a:ℂ)*w)+Complex.exp ((b:ℂ)*w))/2)
  rw [norm_one,norm_div,Complex.norm_two] at hrev
  change 1-(Real.exp (a*w.re)+Real.exp (b*w.re))/2 ≤
    ‖1-(Complex.exp ((a:ℂ)*w)+Complex.exp ((b:ℂ)*w))/2‖
  linarith only [htri,hrev]

lemma exp_clock_decomposition (a : ℝ) (w : ℂ) :
    Complex.exp ((a:ℂ)*w) = (Real.exp (a*w.re):ℂ)*
      Complex.exp (((a*w.im:ℝ):ℂ)*I) := by
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- Away from its simple zero, the two-prime averaged-clock denominator is
polynomially bounded below on the entire closed left half-plane. -/
theorem exists_two_prime_clockDefect_lower {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ w : ℂ, w.re ≤ 0 → r ≤ ‖w‖ →
      c/(2+|w.im|)^N ≤ ‖clockDefect (Real.log p) (Real.log q) w‖ := by
  obtain ⟨c,C,hc,hC,hsep⟩ := exists_two_prime_chord_separation hp hq hpq
  let a := Real.log p
  let b := Real.log q
  have ha : 0 < a := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < b := Real.log_pos (by exact_mod_cast hq.one_lt)
  let ra := Real.exp (-a*r/2)
  let rb := Real.exp (-b*r/2)
  have hra0 : 0 < ra := Real.exp_pos _
  have hrb0 : 0 < rb := Real.exp_pos _
  have hra : ra < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos ha hr])
  have hrb : rb < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hb hr])
  let η := min ra rb
  have hη : 0 < η := lt_min hra0 hrb0
  let μ := min (r/2) 1
  have hμ : 0 < μ := lt_min (by positivity) zero_lt_one
  let cr := 1-(ra+rb)/2
  have hcr : 0 < cr := by dsimp only [cr]; linarith only [hra,hrb]
  let cp := η*c^2*μ^2/8
  have hcp : 0 < cp := by dsimp only [cp]; positivity
  let N : ℕ := ⌈2*C⌉₊
  have hN : 2*C ≤ (N:ℝ) := Nat.le_ceil _
  refine ⟨min cr cp,lt_min hcr hcp,N,?_⟩
  intro w hw hrw
  have hbase : 1 ≤ 2+|w.im| := by linarith only [abs_nonneg w.im]
  have hbase0 : 0 < 2+|w.im| := by positivity
  have hden : 0 < (2+|w.im|)^N := pow_pos hbase0 N
  by_cases hx : r/2 ≤ -w.re
  · have hpa : Real.exp (a*w.re) ≤ ra := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hx ha.le]
    have hpb : Real.exp (b*w.re) ≤ rb := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hx hb.le]
    have hrad : cr ≤ ‖clockDefect a b w‖ := by
      have hh := clockDefect_radial_lower a b w
      dsimp only [cr]
      linarith only [hh,hpa,hpb]
    exact ((div_le_self (le_of_lt (lt_min hcr hcp)) (one_le_pow₀ hbase)).trans
      (min_le_left cr cp)).trans hrad
  · have hreal : -r/2 ≤ w.re := by linarith only [lt_of_not_ge hx]
    have him : r/2 ≤ |w.im| := by
      have hh := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_nonpos hw] at hh
      linarith only [hh,hrw,lt_of_not_ge hx]
    let A := ‖Complex.exp (((a*w.im:ℝ):ℂ)*I)-1‖
    let B := ‖Complex.exp (((b*w.im:ℝ):ℂ)*I)-1‖
    have hA : 0 ≤ A := norm_nonneg _
    have hB : 0 ≤ B := norm_nonneg _
    have hphase : c*min |w.im| ((2+|w.im|)^(-C)) ≤ A+B := by
      simpa only [A,B,a,b,mul_comm] using hsep w.im
    have hηa : η ≤ Real.exp (a*w.re) := (min_le_left ra rb).trans
      (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hreal ha.le]))
    have hηb : η ≤ Real.exp (b*w.re) := (min_le_right ra rb).trans
      (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hreal hb.le]))
    have hpa : Real.exp (a*w.re) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le hw)
    have hpb : Real.exp (b*w.re) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hb.le hw)
    have hquad : η/4*(A^2+B^2) ≤ ‖clockDefect a b w‖ := by
      have hh := averaged_chord_defect_lower
        (Complex.norm_exp_ofReal_mul_I (a*w.im)) (Complex.norm_exp_ofReal_mul_I (b*w.im))
        hpa hpb hηa hηb
      rw [norm_sub_rev (1:ℂ),norm_sub_rev (1:ℂ)] at hh
      have he : clockDefect a b w = 1-((Real.exp (a*w.re):ℂ)*
          Complex.exp (((a*w.im:ℝ):ℂ)*I)+(Real.exp (b*w.re):ℂ)*
          Complex.exp (((b*w.im:ℝ):ℂ)*I))/2 := by
        rw [clockDefect,exp_clock_decomposition a w,exp_clock_decomposition b w]
      rw [← he] at hh
      exact hh.trans (Complex.re_le_norm _)
    let P : ℝ := (2+|w.im|)^(-C)
    have hP0 : 0 ≤ P := Real.rpow_nonneg hbase0.le _
    have hP1 : P ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith only [hC])
    have hmin : μ*P ≤ min |w.im| P := by
      apply le_min
      · exact ((mul_le_of_le_one_right hμ.le hP1).trans (min_le_left (r/2) 1)).trans him
      · exact mul_le_of_le_one_left hP0 (min_le_right (r/2) 1)
    have htotal : c*μ*P ≤ A+B := by
      have hh := mul_le_mul_of_nonneg_left hmin hc.le
      dsimp only [P] at hh
      nlinarith only [hh,hphase]
    have htotal2 := pow_le_pow_left₀ (by positivity : 0 ≤ c*μ*P) htotal 2
    have hquad2 : cp*P^2 ≤ ‖clockDefect a b w‖ := by
      have hh := mul_le_mul_of_nonneg_left htotal2 hη.le
      have hdif := mul_nonneg hη.le (sq_nonneg (A-B))
      dsimp only [cp]
      nlinarith only [hh,hdif,hquad]
    have hpow : 1/(2+|w.im|)^N ≤ P^2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le hbase (neg_le_neg hN)
      have he : -(2*C)=(-C)*2 := by ring
      rw [Real.rpow_neg hbase0.le,Real.rpow_natCast,he,Real.rpow_mul hbase0.le,Real.rpow_two] at hh
      simpa only [one_div,P] using hh
    calc
      min cr cp/(2+|w.im|)^N ≤ cp/(2+|w.im|)^N :=
        div_le_div_of_nonneg_right (min_le_right cr cp) hden.le
      _ = cp*(1/(2+|w.im|)^N) := by ring
      _ ≤ cp*P^2 := mul_le_mul_of_nonneg_left hpow hcp.le
      _ ≤ _ := hquad2

#print axioms exists_two_prime_chord_separation
#print axioms averaged_chord_defect_lower
#print axioms exists_two_prime_clockDefect_lower
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
