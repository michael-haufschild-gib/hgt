import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Associative quantum composition by Dirichlet convolution

A shell of a composite gas counts every ordered pair of microscopic states on
two factors. Raising the fraction belonging to a factorization to a complex
power gives amplitudes that compose associatively. On each nonvacuum shell
the sum of their Born weights equals one precisely on the critical line.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

/-- Positive shell multiplicities, with Dirichlet convolution as composition. -/
def positiveProfiles : Subsemigroup (ArithmeticFunction ℕ) where
  carrier := {F | ∀ n : ℕ, 0 < n → 0 < F n}
  mul_mem' := by
    intro F G hF hG n hn
    have hm : (1,n) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, hn.ne'⟩
    exact (Nat.mul_pos (hF 1 Nat.one_pos) (hG n hn)).trans_le
      (Finset.single_le_sum (f := fun d : ℕ × ℕ => F d.1 * G d.2) (fun _ _ => Nat.zero_le _) hm)

abbrev Profile := ↥positiveProfiles

/-- Complex power of a shell multiplicity; only positive arguments occur on physical shells. -/
def multiplicityPower (s : ℂ) (m : ℕ) := Complex.exp (s * (Real.log m : ℂ))

private theorem power_ne (s : ℂ) (m : ℕ) : multiplicityPower s m ≠ 0 := Complex.exp_ne_zero _

/-- The fraction of pair states belonging to (a,b), raised to the power s. -/
def compositionAmplitude (s : ℂ) (F G : Profile) (a b : ℕ) : ℂ :=
  multiplicityPower s (F.val a) * multiplicityPower s (G.val b) /
    multiplicityPower s ((F*G).val (a*b))

/-- Both bracketings give the same complex amplitude for every triple of factors. -/
theorem compositionAmplitude_assoc (s : ℂ) (F G H : Profile) (a b c : ℕ) :
    compositionAmplitude s (F*G) H (a*b) c * compositionAmplitude s F G a b =
      compositionAmplitude s F (G*H) a (b*c) * compositionAmplitude s G H b c := by
  simp only [compositionAmplitude, mul_assoc (F : Profile) G H, mul_assoc a b c]
  field_simp [power_ne]

def share (F G : Profile) (n : ℕ) (d : ℕ × ℕ) : ℝ :=
  (F.val d.1 : ℝ) * (G.val d.2 : ℝ) / ((F*G).val n : ℝ)

private theorem share_pos (F G : Profile) {n : ℕ} {d : ℕ × ℕ} (hd : d ∈ n.divisorsAntidiagonal) :
    0 < share F G n d := by
  obtain ⟨ha, hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hd
  exact div_pos (mul_pos (Nat.cast_pos.mpr (F.property _ (Nat.pos_of_ne_zero ha)))
    (Nat.cast_pos.mpr (G.property _ (Nat.pos_of_ne_zero hb))))
    (Nat.cast_pos.mpr ((F*G).property n (Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hd).2)))

theorem sum_share (F G : Profile) (n : ℕ+) :
    ∑ d ∈ (n : ℕ).divisorsAntidiagonal, share F G n d = 1 := by
  simp only [share, ← Finset.sum_div, ← Nat.cast_mul, ← Nat.cast_sum]
  exact div_self (Nat.cast_ne_zero.mpr ((F*G).property n n.pos).ne')

private theorem power_norm (s : ℂ) (m : ℕ) :
    ‖multiplicityPower s m‖ = Real.exp (s.re * Real.log m) := by
  simp only [multiplicityPower, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem compositionAmplitude_norm_sq (s : ℂ) (F G : Profile) {n : ℕ} {d : ℕ × ℕ}
    (hd : d ∈ n.divisorsAntidiagonal) :
    ‖compositionAmplitude s F G d.1 d.2‖ ^ 2 = share F G n d ^ (2*s.re) := by
  have hprod := Nat.mem_divisorsAntidiagonal.mp hd
  obtain ⟨ha, hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hd
  have hf : (0 : ℝ) < F.val d.1 := Nat.cast_pos.mpr (F.property _ (Nat.pos_of_ne_zero ha))
  have hg : (0 : ℝ) < G.val d.2 := Nat.cast_pos.mpr (G.property _ (Nat.pos_of_ne_zero hb))
  have hfg : (0 : ℝ) < (F*G).val n := Nat.cast_pos.mpr ((F*G).property _ (Nat.pos_of_ne_zero hprod.2))
  rw [compositionAmplitude, hprod.1, norm_div, norm_mul, power_norm, power_norm, power_norm,
    ← Real.exp_add, ← Real.exp_sub, sq, ← Real.exp_add, Real.rpow_def_of_pos (share_pos F G hd),
    share, Real.log_div (mul_pos hf hg).ne' hfg.ne', Real.log_mul hf.ne' hg.ne']
  congr 1
  ring

/-- On every nonvacuum shell, each individual factorization has a competing outcome. -/
private theorem share_lt_one (F G : Profile) (n : ℕ+) (hn : 1 < (n : ℕ)) {d : ℕ × ℕ}
    (hd : d ∈ (n : ℕ).divisorsAntidiagonal) : share F G n d < 1 := by
  have h₁ : (1,(n : ℕ)) ∈ (n : ℕ).divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, n.ne_zero⟩
  have h₂ : ((n : ℕ),1) ∈ (n : ℕ).divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one _, n.ne_zero⟩
  have alt : ∃ e ∈ (n : ℕ).divisorsAntidiagonal, e ≠ d := by
    by_cases h : (1,(n : ℕ)) = d
    · exact ⟨_, h₂, fun he => hn.ne (congrArg Prod.fst (h.trans he.symm))⟩
    · exact ⟨_, h₁, h⟩
  obtain ⟨e, he, hne⟩ := alt
  rw [← sum_share F G n]
  exact Finset.single_lt_sum hne hd he (share_pos F G he) (fun i hi _ => (share_pos F G hi).le)

/-- Strict decrease of all Born weights selects the same exponent for every pair of profiles. -/
theorem composition_shell_unit_iff (s : ℂ) (F G : Profile) (n : {k : ℕ+ // 1 < (k : ℕ)}) :
    (∑ d ∈ (n.val : ℕ).divisorsAntidiagonal, ‖compositionAmplitude s F G d.1 d.2‖ ^ 2) = 1 ↔
      s.re = 1/2 := by
  let M (x : ℝ) := ∑ d ∈ (n.val : ℕ).divisorsAntidiagonal, share F G n.val d ^ x
  have hM : StrictAnti M := by
    intro x y hxy
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨(1,_), Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, n.val.ne_zero⟩⟩
    · intro d hd
      exact Real.strictAnti_rpow_of_base_lt_one (share_pos F G hd) (share_lt_one F G _ n.2 hd) hxy
  have h₁ : M 1 = 1 := by simpa only [M, Real.rpow_one] using sum_share F G n.val
  have he : (∑ d ∈ (n.val : ℕ).divisorsAntidiagonal, ‖compositionAmplitude s F G d.1 d.2‖^2) =
      M (2*s.re) := Finset.sum_congr rfl (fun _ hd => compositionAmplitude_norm_sq _ _ _ hd)
  rw [he, ← h₁, hM.injective.eq_iff]
  constructor <;> intro h <;> linarith

theorem composition_vacuum (s : ℂ) (F G : Profile) : compositionAmplitude s F G 1 1 = 1 := by
  have hF : (0 : ℝ) < F.val 1 := Nat.cast_pos.mpr (F.property 1 Nat.one_pos)
  have hG : (0 : ℝ) < G.val 1 := Nat.cast_pos.mpr (G.property 1 Nat.one_pos)
  rw [compositionAmplitude, one_mul]
  change _ / multiplicityPower s ((F.val * G.val) 1) = 1
  rw [ArithmeticFunction.mul_apply_one, div_eq_one_iff_eq (power_ne s _)]
  simp only [multiplicityPower, Nat.cast_mul, Real.log_mul hF.ne' hG.ne',
    Complex.ofReal_add, mul_add, Complex.exp_add]

/-- A single residue on each shell of the second gas. -/
def singleProfile : Profile :=
  ⟨ArithmeticFunction.zeta, fun n hn => by rw [ArithmeticFunction.zeta_apply_ne hn.ne']; exact Nat.one_pos⟩

/-- Microscopic states of the first gas are generators of a cyclic group. -/
def orderProfile : Profile :=
  ⟨⟨Nat.totient, Nat.totient_zero⟩, fun _ hn => Nat.totient_pos.mpr hn⟩

theorem order_single_multiplicity (n : ℕ) : (orderProfile * singleProfile).val n = n := by
  change (orderProfile.val * ArithmeticFunction.zeta) n = _
  rw [ArithmeticFunction.mul_zeta_apply]
  exact Nat.sum_totient n

private theorem half_power (m : ℕ) (hm : 0 < m) :
    multiplicityPower (1/2) m = (Real.sqrt m : ℂ) := by
  have h : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [multiplicityPower, show (1/2 : ℂ) * (Real.log (m : ℕ) : ℂ) =
      ((Real.log (m : ℕ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Real.exp_half, Real.exp_log h]

/-- The original order channel differs by exactly the outgoing order phase on the critical line. -/
theorem composition_order_channel (s : ℂ) (a b : ℕ+) :
    compositionAmplitude s orderProfile singleProfile a b =
      multiplicityPower (s-1/2) (a : ℕ).totient * channel s (a*b) a := by
  have h₁ : singleProfile.val b = 1 := ArithmeticFunction.zeta_apply_ne b.ne_zero
  have ha : 0 < (a : ℕ).totient := Nat.totient_pos.mpr a.pos
  have hs : multiplicityPower s (a : ℕ).totient =
      multiplicityPower (s-1/2) (a : ℕ).totient * (Real.sqrt (a : ℕ).totient : ℂ) := by
    rw [← half_power _ ha]
    simp only [multiplicityPower, ← Complex.exp_add]
    congr 1
    ring
  have invwave : (multiplicityPower s ((a*b : ℕ+) : ℕ))⁻¹ = heat s (a*b) := by
    rw [multiplicityPower, ← Complex.exp_neg, heat, energy, neg_mul]
  rw [compositionAmplitude, order_single_multiplicity, h₁]
  change multiplicityPower s (a : ℕ).totient * multiplicityPower s 1 / _ = _
  rw [hs, show multiplicityPower s 1 = 1 by simp [multiplicityPower], mul_one, div_eq_mul_inv,
    ← PNat.mul_coe, invwave, channel, mul_assoc]

theorem outgoing_phase_unit (s : {z : ℂ // z.re = 1/2}) (a : ℕ+) :
    ‖multiplicityPower (s.val-1/2) (a : ℕ).totient‖ = 1 := by
  rw [power_norm, Complex.sub_re, s.2]
  norm_num

#print axioms compositionAmplitude_assoc
#print axioms sum_share
#print axioms compositionAmplitude_norm_sq
#print axioms composition_shell_unit_iff
#print axioms composition_vacuum
#print axioms composition_order_channel
#print axioms outgoing_phase_unit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
