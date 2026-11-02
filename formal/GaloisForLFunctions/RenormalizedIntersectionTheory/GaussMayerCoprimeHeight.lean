import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeSource
import GaloisForLFunctions.RHTower.TotientMulLSeries

/-! Finite primitive-height fibers identify the actual Mayer Green response
at zero with twice the shifted-zeta ratio. -/

open Complex ArithmeticFunction
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeRenewal
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeSource
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeHeight

/-- The reduced residues at a height at least two. -/
def Row (k : ℕ) := {p : Fin (k+2) // Nat.Coprime (k+2) p.val}

instance (k : ℕ) : Fintype (Row k) := inferInstanceAs (Fintype {p : Fin (k+2) // Nat.Coprime (k+2) p.val})

private theorem row_pos (k : ℕ) (p : Row k) : 0 < p.val.val := by
  by_contra h
  have hz : p.val.val=0 := by omega
  have hp := p.property
  rw [hz,Nat.coprime_zero_right] at hp
  omega

private def rowEquiv (k : ℕ) : Row k ≃ {p : ℕ // p < k+2 ∧ Nat.Coprime (k+2) p} where
  toFun p := ⟨p.val.val,p.val.isLt,p.property⟩
  invFun p := ⟨⟨p.val,p.property.1⟩,p.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Height fibers have exactly Euler totient cardinality. -/
theorem card_row (k : ℕ) : Fintype.card (Row k)=Nat.totient (k+2) := by
  rw [← Nat.card_eq_fintype_card,Nat.totient_eq_card_lt_and_coprime]
  exact Nat.card_congr (rowEquiv k)

private def rowPair (p : Σ k : ℕ, Row k) : Cone :=
  ⟨(p.2.val.val,p.1+2),row_pos _ _,p.2.val.isLt,p.2.property.symm⟩

private theorem rowPair_injective : Function.Injective rowPair := by
  rintro ⟨k,p⟩ ⟨l,q⟩ he
  have hk := congrArg (fun p : Cone => p.val.2) he
  change k+2=l+2 at hk
  have hkl : k=l := by omega
  subst l
  have hpq : p=q := by
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun p : Cone => p.val.1) he
  subst q
  rfl

private theorem rowPair_surjective : Function.Surjective rowPair := by
  intro p
  have hp := p.property
  have he : p.val.2-2+2=p.val.2 := by omega
  refine ⟨⟨p.val.2-2,⟨⟨p.val.1,?_⟩,?_⟩⟩,?_⟩
  · rw [he]
    exact hp.2.1
  · change Nat.Coprime (p.val.2-2+2) p.val.1
    rw [he]
    exact hp.2.2.symm
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact he

/-- The primitive cone split into its finite height fibers. -/
def heightEquiv : Cone ≃ Σ k : ℕ, Row k :=
  (Equiv.ofBijective rowPair ⟨rowPair_injective,rowPair_surjective⟩).symm

private theorem muChi_one : TotientMulLSeries.muChi 1=(fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) := by
  funext n
  by_cases hn : n=0
  · subst n
    simp [TotientMulLSeries.muChi,TotientMulMoebius.chi]
  · simp [TotientMulLSeries.muChi,TotientMulMoebius.chi,hn]

/-- The absolute-chamber totient series, with its actual zeta denominator. -/
theorem totient_series {w : ℂ} (hw : 2 < w.re) :
    LSeries (fun n : ℕ => (Nat.totient n : ℂ)) w=riemannZeta (w-1)/riemannZeta w := by
  have ht := TotientMulLSeries.LSeries_totient_mul 1 (by omega) hw
  simp only [one_mul,Nat.totient_one,Nat.cast_one,muChi_one] at ht
  have hm : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) w * riemannZeta w=1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by linarith only [hw]),mul_comm]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (by linarith only [hw])
  have hz : riemannZeta w ≠ 0 := by
    intro he
    rw [he,mul_zero] at hm
    exact zero_ne_one hm
  apply (eq_div_iff hz).mpr
  rw [ht]
  calc
    _ = (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) w * riemannZeta w) *
        riemannZeta (w-1) := by ring
    _ = _ := by rw [hm,one_mul]

/-- Absolute convergence justifies grouping the actual source by primitive height. -/
theorem coneSum_zero {w : ℂ} (hw : 2 < w.re) :
    (coneSum w).1 zeroPoint=∑' k : ℕ, (Nat.totient (k+2) : ℂ)*((k+2 : ℕ) : ℂ)^(-w) := by
  have hs : Summable (fun p : Cone => (p.val.2 : ℂ)^(-w)) := by
    have h := ((evaluation zeroPoint).hasSum (summable_norm_term hw).of_norm.hasSum).summable
    simpa only [evaluation_apply,term_apply,zeroPoint,mul_zero,zero_add] using h
  have hsigma : Summable (fun p : Σ k : ℕ, Row k => ((heightEquiv.symm p).val.2 : ℂ)^(-w)) :=
    heightEquiv.symm.summable_iff.mpr hs
  rw [coneSum_apply hw]
  simp only [zeroPoint,mul_zero,zero_add]
  rw [← heightEquiv.symm.tsum_eq (fun p : Cone => (p.val.2 : ℂ)^(-w)),hsigma.tsum_sigma]
  apply tsum_congr
  intro k
  change (∑' p : Row k, ((k+2 : ℕ) : ℂ)^(-w))=_
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_row]

private theorem summable_totient {w : ℂ} (hw : 2 < w.re) :
    LSeriesSummable (fun n : ℕ => (Nat.totient n : ℂ)) w := by
  have h := (TotientMulLSeries.summable_id hw).norm
  apply Summable.of_norm
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  by_cases hn : n=0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,norm_div,norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    simp only [Complex.norm_natCast]
    exact_mod_cast Nat.totient_le n

private theorem totient_tail {w : ℂ} (hw : 2 < w.re) :
    LSeries (fun n : ℕ => (Nat.totient n : ℂ)) w=
      1+∑' k : ℕ, (Nat.totient (k+2) : ℂ)*((k+2 : ℕ) : ℂ)^(-w) := by
  have hs := summable_totient hw
  have hs1 := (summable_nat_add_iff (f := LSeries.term (fun n : ℕ => (Nat.totient n : ℂ)) w) 1).mpr hs
  rw [LSeries,hs.tsum_eq_zero_add,hs1.tsum_eq_zero_add]
  have h0 : LSeries.term (fun n : ℕ => (Nat.totient n : ℂ)) w 0=0 := by simp
  have h1 : LSeries.term (fun n : ℕ => (Nat.totient n : ℂ)) w 1=1 := by
    rw [LSeries.term_of_ne_zero (by omega)]
    simp
  rw [h0,zero_add,h1]
  congr 1
  apply tsum_congr
  intro k
  rw [LSeries.term_of_ne_zero (by omega),Complex.cpow_neg,div_eq_mul_inv]

/-- The actual Green response has the independently normalized totient value at zero. -/
theorem green_zero {w : ℂ} (hw : 2 < w.re) :
    (green w).1 zeroPoint=2*riemannZeta (w-1)/riemannZeta w := by
  change 1+(endpoint w).1 zeroPoint+(2 : ℂ)*(coneSum w).1 zeroPoint=_
  rw [coneSum_zero hw,endpoint_apply]
  simp only [zeroPoint,add_zero,Complex.one_cpow]
  have ht := totient_tail hw
  rw [totient_series hw] at ht
  calc
    _ = 2*(1+∑' k : ℕ, (Nat.totient (k+2) : ℂ)*((k+2 : ℕ) : ℂ)^(-w)) := by ring
    _ = _ := by rw [← ht]; ring

#print axioms coneSum_zero
#print axioms green_zero
#print axioms card_row
#print axioms heightEquiv
#print axioms totient_series

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeHeight
