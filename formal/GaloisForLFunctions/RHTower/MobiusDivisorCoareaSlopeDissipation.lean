import GaloisForLFunctions.RHTower.MobiusDivisorCoareaHeadTransport

/-!
# Dissipation of the actual coarea head slope under every prime merger

Let `g = K - a - 2 f` be the head-action slope, where `K` is nonempty
conditional energy and `a,f` are absolute and signed head masses.
Every prime merger decreases `g` by at least `(h+b)²/b`, where `h,b`
are the signed and absolute masses of its receiving singleton. Zero
absolute mass forces zero signed mass and contributes zero.

The bound follows from conditional Cauchy on every complementary
nonempty pair and exact head transport. It holds for the complete
actual source, with no fibre-sign assumption and no prescribed order.
Isolated pure negative late-prime cells saturate the zero-loss case
identified by the exact late-prime transport law.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Every prime-coordinate merger adds the original absolute masses of its paired cells. -/
theorem mobiusDivisorFibreAbsoluteMass_insert (M : ℕ) (P R : Finset ℕ) (p : ℕ) :
    mobiusDivisorFibreAbsoluteMass M (insert p P) R =
      if p ∈ R then 0 else mobiusDivisorFibreAbsoluteMass M P R +
        mobiusDivisorFibreAbsoluteMass M P (insert p R) :=
  subsetLabelFibre_insert _ _ _ P R p

private lemma mass_zero (M : ℕ) (P R : Finset ℕ)
    (h : mobiusDivisorFibreAbsoluteMass M P R=0) : mobiusDivisorSelectionFibre M P R=0 := by
  apply abs_eq_zero.mp
  exact le_antisymm ((abs_mobiusDivisorSelectionFibre_le_absoluteMass M P R).trans_eq h)
    (abs_nonneg _)

private lemma conditional_pair_le (x y a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hxa : a=0 → x=0) (hyb : b=0 → y=0) :
    (x+y)^2/(a+b) ≤ x^2/a+y^2/b := by
  by_cases haz : a=0
  · simp [haz,hxa haz]
  by_cases hbz : b=0
  · simp [hbz,hyb hbz]
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm haz)
  have hbp : 0<b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hab : a+b≠0 := ne_of_gt (add_pos hap hbp)
  have he : x^2/a+y^2/b-(x+y)^2/(a+b) = (b*x-a*y)^2/(a*b*(a+b)) := by
    field_simp
    ring
  have hn : 0 ≤ (b*x-a*y)^2/(a*b*(a+b)) := by positivity
  linarith only [he,hn]

private lemma nonempty_pairs (U : Finset ℕ) {p : ℕ} (hp : p ∈ U)
    (f : Finset ℕ → ℝ) :
    (∑ R ∈ U.powerset.erase ∅,f R) =
      (∑ R ∈ (U.erase p).powerset.erase ∅,(f R+f (insert p R)))+f {p} := by
  have hfull : (∑ R ∈ U.powerset,f R) =
      (∑ R ∈ (U.erase p).powerset,f R)+
        ∑ R ∈ (U.erase p).powerset,f (insert p R) := by
    conv_lhs => rw [← insert_erase hp]
    exact sum_powerset_insert (notMem_erase p U) f
  have hhead := sum_erase_add (s := U.powerset) (f := f)
    (by simp : (∅:Finset ℕ) ∈ U.powerset)
  have hbase := sum_erase_add (s := (U.erase p).powerset) (f := f)
    (by simp : (∅:Finset ℕ) ∈ (U.erase p).powerset)
  have hchild := sum_erase_add (s := (U.erase p).powerset) (f := fun R => f (insert p R))
    (by simp : (∅:Finset ℕ) ∈ (U.erase p).powerset)
  simp only [insert_empty_eq] at hchild
  rw [sum_add_distrib]
  linarith only [hfull,hhead,hbase,hchild]

/-- Nonempty conditional energy loses at least the singleton energy transferred to the head. -/
theorem mobiusDivisorNonemptyCoarea_insert_le (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) :
    mobiusDivisorNonemptyCoarea M (insert p P) ≤ mobiusDivisorNonemptyCoarea M P -
      (mobiusDivisorSelectionFibre M P {p})^2 / mobiusDivisorFibreAbsoluteMass M P {p} := by
  have hpU : p ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩
  let f := fun P R => (mobiusDivisorSelectionFibre M P R)^2/mobiusDivisorFibreAbsoluteMass M P R
  have hz (R : Finset ℕ) : f (insert p P) (insert p R)=0 := by
    simp [f,mobiusDivisorSelectionFibre_insert,mobiusDivisorFibreAbsoluteMass_insert]
  have hafter : mobiusDivisorNonemptyCoarea M (insert p P) =
      ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset.erase ∅,f (insert p P) R := by
    unfold mobiusDivisorNonemptyCoarea
    rw [nonempty_pairs _ hpU]
    change (∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset.erase ∅,
      (f (insert p P) R+f (insert p P) (insert p R)))+f (insert p P) (insert p ∅)=_
    simp only [hz,add_zero]
  have hbefore : mobiusDivisorNonemptyCoarea M P-f P {p} =
      ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset.erase ∅,(f P R+f P (insert p R)) := by
    unfold mobiusDivisorNonemptyCoarea
    rw [nonempty_pairs _ hpU]
    change (_+f P {p})-f P {p}=_
    ring
  rw [hafter]
  change _ ≤ mobiusDivisorNonemptyCoarea M P-f P {p}
  rw [hbefore]
  apply sum_le_sum
  intro R hR
  have hpR : p ∉ R := by
    intro h
    have hh := mem_powerset.mp (mem_erase.mp hR).2 h
    exact (mem_erase.mp hh).1 rfl
  dsimp [f]
  rw [mobiusDivisorSelectionFibre_insert,mobiusDivisorFibreAbsoluteMass_insert]
  simp only [if_neg hpR]
  exact conditional_pair_le _ _ _ _ (mobiusDivisorFibreAbsoluteMass_nonneg M P R)
    (mobiusDivisorFibreAbsoluteMass_nonneg M P (insert p R))
    (mass_zero M P R) (mass_zero M P (insert p R))

/-- Every actual prime merger dissipates slope by at least the squared shifted singleton
mass divided by its absolute mass. -/
theorem mobiusDivisorCoareaHeadSlope_insert_loss_ge (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) :
    (mobiusDivisorSelectionFibre M P {p}+mobiusDivisorFibreAbsoluteMass M P {p})^2 /
        mobiusDivisorFibreAbsoluteMass M P {p} ≤
      mobiusDivisorCoareaHeadSlope M P-mobiusDivisorCoareaHeadSlope M (insert p P) := by
  have hK := mobiusDivisorNonemptyCoarea_insert_le M P hp hpM
  have hid : (mobiusDivisorSelectionFibre M P {p}+mobiusDivisorFibreAbsoluteMass M P {p})^2 /
      mobiusDivisorFibreAbsoluteMass M P {p} =
      (mobiusDivisorSelectionFibre M P {p})^2/mobiusDivisorFibreAbsoluteMass M P {p}+
        mobiusDivisorFibreAbsoluteMass M P {p}+2*mobiusDivisorSelectionFibre M P {p} := by
    by_cases hz : mobiusDivisorFibreAbsoluteMass M P {p}=0
    · simp [hz,mass_zero M P {p} hz]
    · field_simp
      ring
  unfold mobiusDivisorCoareaHeadSlope
  rw [mobiusDivisorFibreAbsoluteMass_insert,mobiusDivisorSelectionFibre_insert]
  simp only [notMem_empty,if_false,insert_empty_eq]
  rw [hid]
  linarith only [hK]

/-- The coarea head slope is nonincreasing under every prime merger, without sign assumptions. -/
theorem mobiusDivisorCoareaHeadSlope_insert_le (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) :
    mobiusDivisorCoareaHeadSlope M (insert p P) ≤ mobiusDivisorCoareaHeadSlope M P := by
  have h := mobiusDivisorCoareaHeadSlope_insert_loss_ge M P hp hpM
  have hn : 0 ≤ (mobiusDivisorSelectionFibre M P {p}+mobiusDivisorFibreAbsoluteMass M P {p})^2 /
      mobiusDivisorFibreAbsoluteMass M P {p} :=
    div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg M P {p})
  linarith only [h,hn]

end RHTower
