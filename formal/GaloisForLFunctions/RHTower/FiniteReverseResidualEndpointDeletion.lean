import GaloisForLFunctions.RHTower.FiniteReverseResidualBranchMoments
import GaloisForLFunctions.RHTower.FiniteOneHeadResidualWindow

/-!
# Endpoint deletion identities for finite reverse moment carriers

Removing one distinguished atom from either the reverse lower head or the
uniform-tail upper head leaves a residual vector selected by the continuous
finite rank fold. These identities retain complete padded vectors.
-/

namespace RHTower
noncomputable section

/-- Removing one large atom from a reverse head leaves its canonical
residual vector, padded to any larger common count. -/
theorem reverse_head_delete_large_selector
    {E F a b : ℝ} {n K : ℕ}
    (hn : 10 ≤ n) (hKn : n ≤ K) (ha : 0 < a)
    (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=E)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=F) :
    reverseResidualSelectorAux (E-a) (F-a^2) (K-1) (K-3) =
      reverseResidualVector (E-a) (F-a^2) (K-1) (n-1) := by
  have hcast : (((n-1:ℕ):ℝ)-1) = (n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hresfirst : (((n-1:ℕ):ℝ)-1)*a+b=E-a := by
    rw [hcast, ← hfirst]
    ring
  have hressecond : (((n-1:ℕ):ℝ)-1)*a^2+b^2=F-a^2 := by
    rw [hcast, ← hsecond]
    ring
  have hnr : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hApos : 0 < E-a := by
    have hval : E-a=((n:ℝ)-2)*a+b := by rw [←hfirst]; ring
    rw [hval]
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha) hb
  have hrank2 : (2:ℝ) ≤ (E-a)^2/(F-a^2) := by
    have hlow := (ordered_twoLevel_effectiveRank_interval
      (show 2 ≤ n-1 by omega) ha hb hba hresfirst hressecond).2.1
    rw [hcast] at hlow
    linarith
  exact ordered_twoLevel_selector_eq
    (show 3 ≤ n-1 by omega) (show n-1 ≤ (K-3)+2 by omega)
    hApos ha hb hba hresfirst hressecond hrank2

/-- Removing the distinguished large atom from a uniform-tail head leaves
the canonical equal-atom residual vector. -/
theorem uniform_tail_delete_large_selector
    {E F L s : ℝ} {N : ℕ} (hN : 10 ≤ N) (hs : 0 < s)
    (hfirst : L+((N:ℝ)-1)*s=E)
    (hsecond : L^2+((N:ℝ)-1)*s^2=F) :
    reverseResidualSelectorAux (E-L) (F-L^2) (N-1) (N-3) =
      reverseResidualVector (E-L) (F-L^2) (N-1) (N-1) := by
  have hcast : (((N-1:ℕ):ℝ)-1) = (N:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  have hresfirst : (((N-1:ℕ):ℝ)-1)*s+s=E-L := by
    rw [hcast, ←hfirst]
    ring
  have hressecond : (((N-1:ℕ):ℝ)-1)*s^2+s^2=F-L^2 := by
    rw [hcast, ←hsecond]
    ring
  have hNr : (10:ℝ) ≤ N := by exact_mod_cast hN
  have hApos : 0 < E-L := by
    rw [←hfirst]
    have hfactor : 0 < (N:ℝ)-1 := by linarith
    nlinarith [mul_pos hfactor hs]
  have hrank2 : (2:ℝ) ≤ (E-L)^2/(F-L^2) := by
    have hlow := (ordered_twoLevel_effectiveRank_interval
      (show 2 ≤ N-1 by omega) hs hs.le le_rfl hresfirst hressecond).2.1
    rw [hcast] at hlow
    linarith
  exact ordered_twoLevel_selector_eq
    (show 3 ≤ N-1 by omega) (show N-1 ≤ (N-3)+2 by omega)
    hApos hs hs.le le_rfl hresfirst hressecond hrank2

/-- A selector endpoint identified with an ordered two-level head has that
head's cubic power sum, including all padded zero slots. -/
theorem reverseResidualSelector_cubic_of_ordered_endpoint
    {A B a b : ℝ} {N j n : ℕ}
    (hn : 2 ≤ n) (hnN : n ≤ N) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=A)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=B)
    (hsel : reverseResidualSelectorAux A B N j =
      reverseResidualVector A B N n) :
    (∑ i : Fin N, (reverseResidualSelectorAux A B N j i)^3) =
      ((n:ℝ)-1)*a^3+b^3 := by
  obtain ⟨haeq, hbeq⟩ := reverseResidual_unique hn hba hfirst hsecond
  rw [hsel]
  simpa only [←haeq, ←hbeq] using
    reverseResidualVector_pow_sum A B N n 3 hnN hn (by omega)

/-- Any positive ordered residual head whose count fits the available slots
certifies both sides of the one-head positive moment cone. -/
theorem oneHeadResidualAdmissible_of_ordered_head
    {E F x a b : ℝ} {M n : ℕ} (hn : 3 ≤ n)
    (hnM : n ≤ M-1) (hx : 0 ≤ x)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hresA : ((n:ℝ)-1)*a+b=E-x)
    (hresB : ((n:ℝ)-1)*a^2+b^2=F-x^2) :
    OneHeadResidualAdmissible E F M x := by
  obtain ⟨hBpos, hrlow, hrhigh, _⟩ :=
    ordered_twoLevel_effectiveRank_interval (show 2 ≤ n by omega)
      ha hb hba hresA hresB
  have hnr : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hApos : 0 < E-x := by
    rw [←hresA]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by linarith) ha) hb
  have hlowmul : ((n:ℝ)-1)*(F-x^2) ≤ (E-x)^2 :=
    (le_div_iff₀ hBpos).mp hrlow
  have huppmul : (E-x)^2 ≤ (n:ℝ)*(F-x^2) :=
    (div_le_iff₀ hBpos).mp hrhigh
  have hupper : F-x^2 ≤ (E-x)^2 := by
    have hscale := mul_nonneg (by linarith : 0 ≤ (n:ℝ)-2) hBpos.le
    nlinarith
  have hMreal : (n:ℝ) ≤ (M:ℝ)-1 := by
    have hMone : 1 ≤ M := by omega
    have hc : (((M-1:ℕ):ℝ))=(M:ℝ)-1 := by
      rw [Nat.cast_sub hMone]
      norm_num
    rw [←hc]
    exact_mod_cast hnM
  have hbudget : 0 ≤ oneHeadResidualBudget E F M x := by
    unfold oneHeadResidualBudget
    have hscale := mul_nonneg (sub_nonneg.mpr hMreal) hBpos.le
    nlinarith
  exact ⟨hx,hApos,hBpos,hbudget,hupper⟩

/-- Deleting one large atom from the reverse lower head preserves its full
cubic trace after finite-fold selection and zero padding. -/
theorem reverse_head_delete_large_cubic
    {E F a b : ℝ} {n K : ℕ}
    (hn : 10 ≤ n) (hKn : n ≤ K) (ha : 0 < a)
    (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=E)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=F) :
    a^3 + (∑ i : Fin (K-1),
      (reverseResidualSelectorAux (E-a) (F-a^2) (K-1) (K-3) i)^3) =
      ((n:ℝ)-1)*a^3+b^3 := by
  have hcast : (((n-1:ℕ):ℝ)-1) = (n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hresA : (((n-1:ℕ):ℝ)-1)*a+b=E-a := by
    rw [hcast, ←hfirst]
    ring
  have hresB : (((n-1:ℕ):ℝ)-1)*a^2+b^2=F-a^2 := by
    rw [hcast, ←hsecond]
    ring
  have hsel := reverse_head_delete_large_selector hn hKn ha hb hba hfirst hsecond
  have hsum := reverseResidualSelector_cubic_of_ordered_endpoint
    (show 2 ≤ n-1 by omega) (show n-1 ≤ K-1 by omega)
    hba hresA hresB hsel
  rw [hsum, hcast]
  ring

/-- The upper head with one large atom and a uniform tail likewise retains
its full cubic trace after selecting the residual tail. -/
theorem uniform_tail_delete_large_cubic
    {E F L s : ℝ} {N : ℕ} (hN : 10 ≤ N) (hs : 0 < s)
    (hfirst : L+((N:ℝ)-1)*s=E)
    (hsecond : L^2+((N:ℝ)-1)*s^2=F) :
    L^3 + (∑ i : Fin (N-1),
      (reverseResidualSelectorAux (E-L) (F-L^2) (N-1) (N-3) i)^3) =
      L^3+((N:ℝ)-1)*s^3 := by
  have hcast : (((N-1:ℕ):ℝ)-1) = (N:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  have hresA : (((N-1:ℕ):ℝ)-1)*s+s=E-L := by
    rw [hcast, ←hfirst]
    ring
  have hresB : (((N-1:ℕ):ℝ)-1)*s^2+s^2=F-L^2 := by
    rw [hcast, ←hsecond]
    ring
  have hsel := uniform_tail_delete_large_selector hN hs hfirst hsecond
  have hsum := reverseResidualSelector_cubic_of_ordered_endpoint
    (show 2 ≤ N-1 by omega) (le_refl (N-1))
    le_rfl hresA hresB hsel
  rw [hsum, hcast]
  ring

/-- A reverse lower head, padded to a larger common count, is admitted at
its distinguished large atom. -/
theorem reverse_head_delete_large_admissible
    {E F a b : ℝ} {n K : ℕ}
    (hn : 10 ≤ n) (hKn : n ≤ K) (ha : 0 < a)
    (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=E)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=F) :
    OneHeadResidualAdmissible E F K a := by
  have hcast : (((n-1:ℕ):ℝ)-1) = (n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hresA : (((n-1:ℕ):ℝ)-1)*a+b=E-a := by
    rw [hcast, ←hfirst]
    ring
  have hresB : (((n-1:ℕ):ℝ)-1)*a^2+b^2=F-a^2 := by
    rw [hcast, ←hsecond]
    ring
  exact oneHeadResidualAdmissible_of_ordered_head
    (show 3 ≤ n-1 by omega) (show n-1 ≤ K-1 by omega)
    ha.le ha hb hba hresA hresB

/-- A large atom with a positive uniform tail is admitted at its total
head count. -/
theorem uniform_tail_delete_large_admissible
    {E F L s : ℝ} {N : ℕ} (hN : 10 ≤ N)
    (hL : 0 ≤ L) (hs : 0 < s)
    (hfirst : L+((N:ℝ)-1)*s=E)
    (hsecond : L^2+((N:ℝ)-1)*s^2=F) :
    OneHeadResidualAdmissible E F N L := by
  have hcast : (((N-1:ℕ):ℝ)-1) = (N:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  have hresA : (((N-1:ℕ):ℝ)-1)*s+s=E-L := by
    rw [hcast, ←hfirst]
    ring
  have hresB : (((N-1:ℕ):ℝ)-1)*s^2+s^2=F-L^2 := by
    rw [hcast, ←hsecond]
    ring
  exact oneHeadResidualAdmissible_of_ordered_head
    (show 3 ≤ N-1 by omega) (le_refl (N-1))
    hL hs hs.le le_rfl hresA hresB

end
end RHTower
