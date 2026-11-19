import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheRightLaplaceZerosOfAConfinedState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConfinedCrossingsAreLocallyFinite

/-!
# Every confined null state detects all but finitely many right zeros

Each invisible conjugate pair costs two negative directions at the state's
own ratio. Window recovery preserves these directions and compactness bounds
their number. At the third crossing at most one pair can be invisible.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Each finite set of upper-right Laplace zeros of a confined null state
forces a smooth window family with at least twice as many negative squares. -/
theorem IsConfinedNullVector.index_ge_twice_upper_zeros {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) (s : Finset (UpperLaplaceZeros F)) :
    ∃ (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ i, IsHalfLineTest (H i)) ∧
      2 * s.card ≤ hermNegIndex (confinedGram r H) := by
  classical
  let n := 2 * s.card
  let e : (s × Bool) ≃ Fin n := (Fintype.equivFin _).trans
    (finCongr (by simp [n, Nat.mul_comm]))
  let B := fun (z : UpperLaplaceZeros F) (b : Bool) =>
    UpperLaplaceZeros.component z (if b then Complex.I else 1)
  let G := fun i : Fin n => B (e.symm i).1.val (e.symm i).2
  have hd (i) : CriticalHalfLineEnergyDomain (G i) :=
    UpperLaplaceZeros.domain_component _ hF.1 _
  have hneg (t : Fin n → ℝ) (ht : t ≠ 0) :
      criticalHalfLineFullEnergy r (fun u => ∑ i, t i * G i u) < 0 := by
    let c := fun z : UpperLaplaceZeros F => if hz : z ∈ s then
      (⟨t (e (⟨z,hz⟩,false)),t (e (⟨z,hz⟩,true))⟩ : ℂ) else 0
    have hc : ∃ z ∈ s, c z ≠ 0 := by
      by_contra! h
      apply ht
      funext i
      obtain ⟨⟨z,b⟩,rfl⟩ := e.surjective i
      have h0 := h z.val z.property
      simp only [c, dif_pos z.property] at h0
      cases b
      · exact congrArg Complex.re h0
      · exact congrArg Complex.im h0
    have eqn : UpperLaplaceZeros.profile s c = fun u => ∑ i, t i * G i u := by
      funext u
      rw [UpperLaplaceZeros.profile, Finset.sum_subtype s (fun _ => Iff.rfl),
        ← e.sum_comp (fun i => t i * G i u), Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      simp only [G, Equiv.symm_apply_apply, Fintype.sum_bool, B, c, dif_pos j.property,
        Bool.false_eq_true, if_false, if_true, UpperLaplaceZeros.component, resolventComponent,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, one_mul, zero_mul, zero_sub]
      ring
    rw [← eqn]
    exact UpperLaplaceZeros.profile_energy_neg s hr hF c hc
  obtain ⟨Y,δ,hY,hδ,hy⟩ := negative_windows_of_strict_domain_family hr hd hneg
  let tag := fun i : Fin n => (i.val : ℝ)
  have htag : Function.Injective tag := fun i j h => Fin.ext (Nat.cast_injective h)
  let S := Finset.univ.image tag
  have hcard : S.card = n := by simp [S, Finset.card_image_of_injective _ htag]
  let f : S ≃ Fin n := S.equivFin.trans (finCongr hcard)
  refine ⟨S,fun i => Y (f i),fun i => hY _,?_⟩
  change n ≤ hermNegIndex ((confinedGram r Y).submatrix f f)
  rw [negIndex_submatrix_equiv]
  exact negIndex_of_negative_window_family hδ hY hy

/-- A confined state at any positive ratio has only finitely many distinct
nonreal Laplace zeros in the open right half-plane, up to conjugation. -/
theorem IsConfinedNullVector.finite_upper_laplace_zeros {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) :
    {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ negativeHalfLineLaplace (cx F) z = 0}.Finite := by
  classical
  obtain ⟨N, hN⟩ := windowIndicesAt_bddAbove hr
  by_contra hinf
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N+1)
  let f : s ↪ UpperLaplaceZeros F :=
    ⟨fun z => ⟨z.val, hs z.property⟩, fun i j h => Subtype.ext (congrArg (fun z : UpperLaplaceZeros F => z.val) h)⟩
  let t := Finset.univ.map f
  obtain ⟨S,H,hH,hindex⟩ := hF.index_ge_twice_upper_zeros hr t
  have cap := hN (show hermNegIndex (confinedGram r H) ∈ windowIndicesAt r from ⟨S,H,hH,rfl⟩)
  have ht : t.card = N+1 := by simpa [t] using hcard
  omega

/-- Crossing the ratio adds the null state itself to all earlier negative
directions. Thus the total right divisor strictly exceeds the dimension
supplied by any set of invisible conjugate pairs. -/
theorem IsConfinedNullVector.right_count_gt_twice_upper_zeros {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) (s : Finset (UpperLaplaceZeros F)) :
    ((2 * s.card + 1 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  classical
  let n := 2*s.card
  obtain ⟨S,H,hH,hn⟩ := hF.index_ge_twice_upper_zeros hr s
  have earlier (k : ℕ) (hk : k ≤ hermNegIndex (confinedGram r H)) :
      ∃ t : Fin k → ℝ, Function.Injective t ∧ ∀ i, 0 < t i ∧ t i < r ∧ ∃ G, IsConfinedNullVector (t i) G := by
    cases k with
    | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k =>
      obtain ⟨t,ht,h⟩ := (confined_index_at_ratio_iff_distinct_critical_ratios k hr).mp ⟨S,H,hH,hk⟩
      exact ⟨t,ht.injective,h⟩
  obtain ⟨t,ht,htc⟩ := earlier n hn
  let v : Fin (n+1) → ℝ := Fin.snoc t r
  have hnew : r ∉ Set.range t := by rintro ⟨i,hi⟩; exact (htc i).2.1.ne hi
  have hv : Function.Injective v := Fin.snoc_injective_iff.mpr ⟨ht,hnew⟩
  have hc (i : Fin (n+1)) : 0 < v i ∧ v i < r+1 ∧ ∃ G, IsConfinedNullVector (v i) G := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [v, Fin.snoc_last]
      exact ⟨hr, lt_add_one r, F, hF⟩
    · simp only [v, Fin.snoc_castSucc]
      exact ⟨(htc j).1, (htc j).2.1.trans (lt_add_one r), (htc j).2.2⟩
  have hp := hr.trans (lt_add_one r)
  obtain ⟨A,Y,hY,hindex⟩ := window_index_of_distinct_critical_ratios hp hv
    (fun i => (hc i).1) (fun i => (hc i).2.1) (fun i => (hc i).2.2)
  exact (confinedIndex_law (n+1)).mp ⟨r+1,hp,A,Y,hY,hindex⟩

/-- Every confined null state detects an actual right zeta zero. Even when
the divisor is finite, the current crossing requires one more negative
direction than all its invisible pairs can provide. -/
theorem IsConfinedNullVector.exists_visible_right_zero {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) :
    ∃ ρ ∈ rightZeros zetaZeroConfig, negativeHalfLineLaplace (cx F) (ρ-1/2) ≠ 0 := by
  classical
  by_contra! hzero
  let hfin := hF.finite_upper_laplace_zeros hr
  let U := hfin.toFinset
  let f : U ↪ UpperLaplaceZeros F := ⟨fun z => ⟨z.val,hfin.mem_toFinset.mp z.property⟩,
    fun i j e => Subtype.ext (congrArg (fun z : UpperLaplaceZeros F => z.val) e)⟩
  let s := Finset.univ.map f
  have hcard : s.card = U.card := by simp [s]
  let D := (U.image fun z : ℂ => z+1/2) ∪ (U.image fun z : ℂ => (starRingEnd ℂ) z+1/2)
  have hd : D.card ≤ 2*U.card := by
    have hunion := Finset.card_union_le (U.image fun z : ℂ => z+1/2)
      (U.image fun z : ℂ => (starRingEnd ℂ) z+1/2)
    have a := Finset.card_image_le (s := U) (f := fun z : ℂ => z+1/2)
    have b := Finset.card_image_le (s := U) (f := fun z : ℂ => (starRingEnd ℂ) z+1/2)
    dsimp only [D]; omega
  have hsub : rightZeros zetaZeroConfig ⊆ (D : Set ℂ) := by
    intro ρ hρ
    let z := ρ-1/2
    have hx : 0 < z.re := by simpa [z,Complex.sub_re] using sub_pos.mpr hρ.2
    have hi : z.im ≠ 0 := by simpa [z] using zetaZeroConfig_im_ne_zero' ρ hρ.1
    have hz := hzero ρ hρ
    rcases lt_or_gt_of_ne hi with h | h
    · apply Finset.mem_union.mpr; right
      refine Finset.mem_image.mpr ⟨(starRingEnd ℂ) z, hfin.mem_toFinset.mpr ⟨by simpa using hx,
        by simpa using h, ?_⟩, by simp [z]⟩
      have he := negativeHalfLineLaplace_real_conj F z
      change negativeHalfLineLaplace (fun u => (F u : ℂ)) z = 0 at hz
      rwa [hz,map_zero] at he
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨z,hfin.mem_toFinset.mpr ⟨hx,h,hz⟩,sub_add_cancel _ _⟩))
  have hle := (hF.right_count_gt_twice_upper_zeros hr s).trans (Set.encard_mono hsub)
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  have hnat : 2*s.card+1 ≤ D.card := by exact_mod_cast hle
  omega

/-- The meromorphic transform of every confined null state has a nonzero
simple-pole residue at a right zeta zero. -/
theorem IsConfinedNullVector.exists_right_residue {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) :
    ∃ ρ ∈ rightZeros zetaZeroConfig, ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun w => (w - (ρ-17/2)) * stateMeromorphic r F w) (𝓝[≠] (ρ-17/2)) (𝓝 c) := by
  obtain ⟨ρ,hρ,hz⟩ := hF.exists_visible_right_zero hr
  exact ⟨ρ,hρ,_,(levyResidue_ne_zero_iff hr hρ.1.1).mpr hz,
    tendsto_stateMeromorphic_residue hF.1 hρ.1.1 hρ.1.2.1⟩

/-- The k-th rung, indexed from zero, can miss at most floor(k/2) distinct
upper-right arguments. This compares the same state with every window. -/
theorem IsCriticalLadder.twice_card_upper_zeros_le {m : ℕ} {R : Fin (m+1) → ℝ}
    {Φ : Fin (m+1) → ℝ → ℝ} (hL : IsCriticalLadder m R Φ) (k : Fin (m+1))
    (s : Finset (UpperLaplaceZeros (Φ k))) : 2 * s.card ≤ k.val := by
  obtain ⟨S,H,hH,hindex⟩ := (hL.null k).index_ge_twice_upper_zeros (hL.pos k) s
  exact hindex.trans (hL.hermNegIndex_confinedGram_le_of_le k (hL.pos k) le_rfl hH)

/-- The third state cannot lose two distinct upper-right modes. -/
theorem IsCriticalLadder.third_state_unique_invisible_pair {R : Fin 3 → ℝ}
    {Φ : Fin 3 → ℝ → ℝ} (hL : IsCriticalLadder 2 R Φ)
    (z w : UpperLaplaceZeros (Φ 2)) : z = w := by
  classical
  by_contra h
  have hbound := hL.twice_card_upper_zeros_le 2 {z,w}
  simp [Finset.card_insert_of_notMem, h] at hbound

/-- All but finitely many nonreal right arguments have nonzero Laplace
value. Reflection supplies the lower quadrant from its upper conjugate. -/
theorem IsConfinedNullVector.finite_nonreal_right_laplace_zeros {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) :
    {z : ℂ | 0 < z.re ∧ z.im ≠ 0 ∧ negativeHalfLineLaplace (cx F) z = 0}.Finite := by
  let U := {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ negativeHalfLineLaplace (cx F) z = 0}
  have hU : U.Finite := hF.finite_upper_laplace_zeros hr
  refine (hU.union (hU.image (starRingEnd ℂ))).subset ?_
  intro z hz
  rcases lt_or_gt_of_ne hz.2.1 with hneg | hpos
  · right
    refine ⟨(starRingEnd ℂ) z, ⟨by simpa using hz.1, by simpa using hneg, ?_⟩, by simp⟩
    exact (negativeHalfLineLaplace_real_conj F z).trans (by rw [show negativeHalfLineLaplace (fun u => (F u : ℂ)) z = 0 from hz.2.2, map_zero])
  · exact Or.inl ⟨hz.1,hpos,hz.2.2⟩

/-- Through any bounded range of ratios a single finite exceptional set works
for all states. Simplicity makes the Laplace zero set independent of the
representative at each of the finitely many crossings. -/
theorem finite_common_exceptions_below (b : ℝ) :
    {z : ℂ | 0 < z.re ∧ z.im ≠ 0 ∧ ∃ (r : ℝ) (F : ℝ → ℝ), 0 < r ∧ r ≤ b ∧
      IsConfinedNullVector r F ∧ negativeHalfLineLaplace (cx F) z = 0}.Finite := by
  classical
  let T := {r : ℝ | 0 < r ∧ r ≤ b ∧ ∃ F, IsConfinedNullVector r F}
  letI : Finite T := (finite_critical_ratios_below b).to_subtype
  choose G hG using fun t : T => t.property.2.2
  have hall := Set.finite_iUnion (fun t : T => (hG t).finite_nonreal_right_laplace_zeros t.property.1)
  refine hall.subset ?_
  rintro z ⟨hx,hy,r,F,hr,hrb,hF,hz⟩
  let t : T := ⟨r, hr, hrb, F, hF⟩
  refine Set.mem_iUnion.mpr ⟨t, hx, hy, ?_⟩
  have eq0 {H : ℝ → ℝ} (h : IsConfinedNullVector r H) : SatisfiesConfinedEigenEquation r 0 H :=
    fun Y hY => by rw [h.2.2 _ hY, zero_mul]
  obtain ⟨-,hp⟩ := confined_eigenfunction_eq_integral_ratio hr hF.1 (hG t).1
    (eq0 hF) (eq0 (hG t)) hF.2.1
  let c := (∫ v, G t v) / (∫ v, F v)
  have he : negativeHalfLineLaplace (cx (G t)) z = (c : ℂ) * negativeHalfLineLaplace (cx F) z := by
    unfold negativeHalfLineLaplace
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hp] with u hu
    change G t u = c * F u at hu
    simp only [cx, hu, Complex.ofReal_mul]
    ring
  rw [he, hz, mul_zero]

/-- An infinite off-line divisor forces infinitely many nonzero simple-pole
residues of every confined state at right zeta zeros. -/
theorem IsConfinedNullVector.finiteOffLine_or_infinite_right_residues {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) :
    BacklundConverse.FiniteOffLine ∨
    {ρ ∈ rightZeros zetaZeroConfig | ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun w => (w - (ρ-17/2)) * stateMeromorphic r F w)
        (𝓝[≠] (ρ-17/2)) (𝓝 c)}.Infinite := by
  classical
  by_cases hfin : BacklundConverse.FiniteOffLine
  · exact Or.inl hfin
  right
  intro hsmall
  apply hfin
  apply ArithmeticOrientationGeometry.rightZeros_zeta_finite_iff_finiteOffLine.mp
  have hbad := (hF.finite_nonreal_right_laplace_zeros hr).image (fun z : ℂ => z + 1/2)
  apply (hsmall.union hbad).subset
  intro ρ hρ
  have hx : 0 < (ρ-(1/2 : ℂ)).re := by
    rw [show (ρ-(1/2 : ℂ)).re = ρ.re-1/2 by norm_num [Complex.sub_re]]
    exact sub_pos.mpr hρ.2
  by_cases hz : negativeHalfLineLaplace (cx F) (ρ-1/2) = 0
  · exact Or.inr ⟨ρ-1/2, ⟨hx, by simpa using zetaZeroConfig_im_ne_zero' ρ hρ.1, hz⟩, sub_add_cancel _ _⟩
  · exact Or.inl ⟨hρ, _, (levyResidue_ne_zero_iff hr hρ.1.1).mpr hz,
      tendsto_stateMeromorphic_residue hF.1 hρ.1.1 hρ.1.2.1⟩

/-- Outside a finite set of locations, every right zeta zero contributes its
nonzero mode to the same confined state, including for an infinite divisor. -/
theorem IsConfinedNullVector.all_but_finitely_many_right_modes {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector r F) :
    ∃ E : Finset ℂ, (∀ q : XiZeroCopy, 0 < (centredZero q).re → centredZero q ∉ E →
      zeroModeCoeff r F q ≠ 0) ∧ ∃ C : ℝ, ∀ t : ℝ, 0 < t →
        ‖(averagedState F t : ℂ) - ∑' q : XiZeroCopy, (if 0 < (centredZero q).re then
          zeroModeCoeff r F q * Complex.exp ((centredZero q-8)*t) else 0)‖ ≤
            C * Real.exp (-(8*t)) := by
  classical
  let h := hF.finite_nonreal_right_laplace_zeros hr
  refine ⟨h.toFinset, ?_, hF.averagedState_sub_rightModes_le hr⟩
  intro q hq he
  have hz : negativeHalfLineLaplace (cx F) (centredZero q) ≠ 0 := by
    intro hx
    exact he (h.mem_toFinset.mpr ⟨hq, im_centredZero_ne_zero q, hx⟩)
  have ha : (criticalAliasCoefficient r : ℂ) ≠ 0 := by exact_mod_cast (criticalAliasCoefficient_positive hr).ne'
  obtain ⟨h9,h10,h11,h12⟩ := averageSymbol_factors_ne_zero (s := centredZero q-8)
    (by rw [show (centredZero q-8).re = (centredZero q).re-8 by simp]; linarith only [hq])
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero ha)) hz)
    (inv_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h9 h10) h11) h12))

#print axioms IsConfinedNullVector.index_ge_twice_upper_zeros
#print axioms IsConfinedNullVector.right_count_gt_twice_upper_zeros
#print axioms IsConfinedNullVector.exists_right_residue
#print axioms IsCriticalLadder.twice_card_upper_zeros_le
#print axioms IsCriticalLadder.third_state_unique_invisible_pair
#print axioms IsConfinedNullVector.finite_nonreal_right_laplace_zeros
#print axioms finite_common_exceptions_below
#print axioms IsConfinedNullVector.finiteOffLine_or_infinite_right_residues
#print axioms IsConfinedNullVector.all_but_finitely_many_right_modes
end GaloisForLFunctions.ExclusionOfTheCriticalState
