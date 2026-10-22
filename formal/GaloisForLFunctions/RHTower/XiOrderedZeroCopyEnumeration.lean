import GaloisForLFunctions.RHTower.XiOrderedPrimeTraceClassRelocation
import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy

open Complex Set

namespace RHTower

noncomputable section

def xiCopiesPos (T : ℝ) : Finset XiZeroCopy :=
  (xiSupportsPos T).biUnion xiZeroCopyFiber

theorem mem_xiCopiesPos {T : ℝ} {q : XiZeroCopy} :
    q ∈ xiCopiesPos T ↔ |(q.1 : ℂ).im| ≤ T ∧ 0 < (q.1 : ℂ).im := by
  classical
  rw [xiCopiesPos, Finset.mem_biUnion]
  constructor
  · rintro ⟨rho, hrho, hq⟩
    rw [mem_xiZeroCopyFiber] at hq
    rw [hq]
    exact mem_xiSupportsPos.mp hrho
  · intro h
    exact ⟨q.1, mem_xiSupportsPos.mpr h, mem_xiZeroCopyFiber.mpr rfl⟩

theorem card_xiCopiesPos (T : ℝ) :
    (xiCopiesPos T).card =
      ∑ rho ∈ xiSupportsPos T, xiSupportMultiplicity rho := by
  classical
  rw [xiCopiesPos, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun rho _ => ?_
    rw [xiZeroCopyFiber, Finset.card_map, Finset.card_univ,
      Fintype.card_fin, xiSupportMultiplicity]
  · intro a _ b _ hab
    exact Finset.disjoint_left.mpr fun q hqa hqb =>
      hab ((mem_xiZeroCopyFiber.mp hqa).symm.trans
        (mem_xiZeroCopyFiber.mp hqb))

theorem intCast_card_xiCopiesPos {T : ℝ} (hT : 0 ≤ T) :
    ((xiCopiesPos T).card : ℤ) = xiZeroCount T := by
  rw [card_xiCopiesPos, xiZeroCount_eq_pos_sum hT]
  push_cast
  rfl

def xiZeroCopyThermalEquiv : ℕ ≃ XiZeroCopy :=
  Equiv.ofBijective xiThermalEnumeration xiThermalEnumeration_bijective

def xiZeroCopyOrderKey (q : XiZeroCopy) : ℝ ×ₗ ℕ :=
  toLex ((q.1 : ℂ).im, xiZeroCopyThermalEquiv.symm q)

theorem xiZeroCopyOrderKey_injective : Function.Injective xiZeroCopyOrderKey := by
  intro q r h
  have hindex : xiZeroCopyThermalEquiv.symm q = xiZeroCopyThermalEquiv.symm r :=
    congrArg (fun x : ℝ ×ₗ ℕ => (ofLex x).2) h
  exact xiZeroCopyThermalEquiv.symm.injective hindex

local instance (priority := 10000) xiZeroCopyLinearOrder : LinearOrder XiZeroCopy :=
  LinearOrder.lift' xiZeroCopyOrderKey xiZeroCopyOrderKey_injective

local instance (priority := 10000) xiZeroCopyLE : LE XiZeroCopy :=
  xiZeroCopyLinearOrder.toLE

local instance (priority := 10000) xiZeroCopyLT : LT XiZeroCopy :=
  xiZeroCopyLinearOrder.toLT

theorem xiZeroCopy_le_iff_key_le {q r : XiZeroCopy} :
    q ≤ r ↔ xiZeroCopyOrderKey q ≤ xiZeroCopyOrderKey r := by
  change (LinearOrder.lift' xiZeroCopyOrderKey
    xiZeroCopyOrderKey_injective).le q r ↔ _
  rfl

theorem xiZeroCopy_lt_iff_key_lt {q r : XiZeroCopy} :
    @LT.lt XiZeroCopy xiZeroCopyLT q r ↔
      xiZeroCopyOrderKey q < xiZeroCopyOrderKey r := by
  change (LinearOrder.lift' xiZeroCopyOrderKey
    xiZeroCopyOrderKey_injective).lt q r ↔ _
  rfl

theorem xiZeroCopy_im_le_of_le {q r : XiZeroCopy} (hqr : q ≤ r) :
    (q.1 : ℂ).im ≤ (r.1 : ℂ).im := by
  have hqr' : xiZeroCopyOrderKey q ≤ xiZeroCopyOrderKey r :=
    xiZeroCopy_le_iff_key_le.mp hqr
  by_contra hnot
  have hrev : xiZeroCopyOrderKey r < xiZeroCopyOrderKey q := by
    rw [xiZeroCopyOrderKey, xiZeroCopyOrderKey,
      Prod.Lex.toLex_lt_toLex]
    exact Or.inl (lt_of_not_ge hnot)
  exact (not_lt_of_ge hqr') hrev

theorem succ_le_card_xiCopiesPos_ordered (n : ℕ) :
    n + 1 ≤ (xiCopiesPos (xiOrderedPositiveOrdinate n)).card := by
  have hcard := intCast_card_xiCopiesPos
    (xiOrderedPositiveOrdinate_nonneg n)
  have hcount := xiOrderedPositiveOrdinate_mem_upperSet n
  change ((n + 1 : ℕ) : ℤ) ≤
    xiZeroCount (xiOrderedPositiveOrdinate n) at hcount
  omega

def xiOrderedPositiveZeroCopy (n : ℕ) : XiZeroCopy :=
  ((Finset.orderIsoOfFin
    (xiCopiesPos (xiOrderedPositiveOrdinate n)) rfl)
      ⟨n, Nat.lt_of_succ_le (succ_le_card_xiCopiesPos_ordered n)⟩).1

theorem xiOrderedPositiveZeroCopy_mem (n : ℕ) :
    xiOrderedPositiveZeroCopy n ∈
      xiCopiesPos (xiOrderedPositiveOrdinate n) := by
  exact ((Finset.orderIsoOfFin
    (xiCopiesPos (xiOrderedPositiveOrdinate n)) rfl)
      ⟨n, Nat.lt_of_succ_le (succ_le_card_xiCopiesPos_ordered n)⟩).2

theorem xiOrderedPositiveZeroCopy_im_eq (n : ℕ) :
    ((xiOrderedPositiveZeroCopy n).1 : ℂ).im =
      xiOrderedPositiveOrdinate n := by
  have hmem := xiOrderedPositiveZeroCopy_mem n
  rw [mem_xiCopiesPos] at hmem
  have himPos : 0 < ((xiOrderedPositiveZeroCopy n).1 : ℂ).im := hmem.2
  have himLe : ((xiOrderedPositiveZeroCopy n).1 : ℂ).im ≤
      xiOrderedPositiveOrdinate n := by
    rw [abs_of_pos himPos] at hmem
    exact hmem.1
  apply le_antisymm himLe
  by_contra hnot
  have himLt : ((xiOrderedPositiveZeroCopy n).1 : ℂ).im <
      xiOrderedPositiveOrdinate n := lt_of_not_ge hnot
  let F : Finset XiZeroCopy := xiCopiesPos (xiOrderedPositiveOrdinate n)
  let e : Fin F.card ≃o ↑F := Finset.orderIsoOfFin F rfl
  have hnF : n < F.card := by
    dsimp [F]
    exact Nat.lt_of_succ_le (succ_le_card_xiCopiesPos_ordered n)
  let iN : Fin F.card := ⟨n, hnF⟩
  have heN : (e iN).1 = xiOrderedPositiveZeroCopy n := by
    simp [e, iN, F, xiOrderedPositiveZeroCopy]
  let G : Finset XiZeroCopy :=
    xiCopiesPos (((xiOrderedPositiveZeroCopy n).1 : ℂ).im)
  let prefMap : Fin (n + 1) → ({q : XiZeroCopy // q ∈ G}) := fun j => by
    let jF : Fin F.card := ⟨j, lt_of_lt_of_le j.isLt
      (succ_le_card_xiCopiesPos_ordered n)⟩
    have hjN : jF ≤ iN := by
      exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    have heLe : (e jF).1 ≤ (e iN).1 := (e.le_iff_le).2 hjN
    have himJLe : (((e jF).1.1 : XiDivisorSupport) : ℂ).im ≤
        (((e iN).1.1 : XiDivisorSupport) : ℂ).im :=
      xiZeroCopy_im_le_of_le heLe
    have heMem : (e jF).1 ∈ F := (e jF).2
    have heMem' : |(((e jF).1.1 : XiDivisorSupport) : ℂ).im| ≤
        xiOrderedPositiveOrdinate n ∧
        0 < (((e jF).1.1 : XiDivisorSupport) : ℂ).im := by
      simpa [F] using (mem_xiCopiesPos.mp heMem)
    refine ⟨(e jF).1, ?_⟩
    rw [mem_xiCopiesPos]
    rw [abs_of_pos heMem'.2]
    exact ⟨by simpa [heN] using himJLe, heMem'.2⟩
  have hprefMapInjective : Function.Injective prefMap := by
    intro j k hjk
    have hval := congrArg Subtype.val hjk
    dsimp [prefMap] at hval
    have hfin := e.injective (Subtype.ext hval)
    apply Fin.ext
    simpa using congrArg Fin.val hfin
  have hcardG : n + 1 ≤ G.card := by
    simpa using Fintype.card_le_of_injective prefMap hprefMapInjective
  have hcountG := intCast_card_xiCopiesPos himPos.le
  have hcount : ((n + 1 : ℕ) : ℤ) ≤
      xiZeroCount (((xiOrderedPositiveZeroCopy n).1 : ℂ).im) := by
    rw [← hcountG]
    exact_mod_cast hcardG
  have hgammaLe := xiOrderedPositiveOrdinate_le_iff.mpr hcount
  linarith

def xiPositiveZeroCopyRank (q : XiZeroCopy) : ℕ :=
  ((xiCopiesPos ((q.1 : ℂ).im)).filter
    (fun r => xiZeroCopyOrderKey r < xiZeroCopyOrderKey q)).card

theorem xiPositiveZeroCopyRank_lt_of_key_lt {q r : XiZeroCopy}
    (hq : 0 < (q.1 : ℂ).im)
    (hqr : xiZeroCopyOrderKey q < xiZeroCopyOrderKey r) :
    xiPositiveZeroCopyRank q < xiPositiveZeroCopyRank r := by
  have himLe : (q.1 : ℂ).im ≤ (r.1 : ℂ).im :=
    by
      have hkey := hqr
      rw [xiZeroCopyOrderKey, xiZeroCopyOrderKey,
        Prod.Lex.toLex_lt_toLex] at hkey
      rcases hkey with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
  have hsub :
      (xiCopiesPos ((q.1 : ℂ).im)).filter
          (fun s => xiZeroCopyOrderKey s < xiZeroCopyOrderKey q) ⊆
        (xiCopiesPos ((r.1 : ℂ).im)).filter
          (fun s => xiZeroCopyOrderKey s < xiZeroCopyOrderKey r) := by
    intro s hs
    rw [Finset.mem_filter] at hs ⊢
    have hsmem := mem_xiCopiesPos.mp hs.1
    refine ⟨mem_xiCopiesPos.mpr ⟨?_, hsmem.2⟩, hs.2.trans hqr⟩
    rw [abs_of_pos hsmem.2] at hsmem ⊢
    exact hsmem.1.trans himLe
  have hqMemRight : q ∈
      (xiCopiesPos ((r.1 : ℂ).im)).filter
        (fun s => xiZeroCopyOrderKey s < xiZeroCopyOrderKey r) := by
    rw [Finset.mem_filter, mem_xiCopiesPos, abs_of_pos hq]
    exact ⟨⟨himLe, hq⟩, hqr⟩
  have hqNotLeft : q ∉
      (xiCopiesPos ((q.1 : ℂ).im)).filter
        (fun s => xiZeroCopyOrderKey s < xiZeroCopyOrderKey q) := by
    simp
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by
    apply hqNotLeft
    rw [heq]
    exact hqMemRight⟩

theorem xiPositiveZeroCopyRank_ordered (n : ℕ) :
    xiPositiveZeroCopyRank (xiOrderedPositiveZeroCopy n) = n := by
  let F : Finset XiZeroCopy := xiCopiesPos (xiOrderedPositiveOrdinate n)
  let e : Fin F.card ≃o ↑F := Finset.orderIsoOfFin F rfl
  have hnF : n < F.card := by
    dsimp [F]
    exact Nat.lt_of_succ_le (succ_le_card_xiCopiesPos_ordered n)
  let iN : Fin F.card := ⟨n, hnF⟩
  have heN : (e iN).1 = xiOrderedPositiveZeroCopy n := by
    simp [e, iN, F, xiOrderedPositiveZeroCopy]
  let P : Finset XiZeroCopy :=
    (xiCopiesPos (((xiOrderedPositiveZeroCopy n).1 : ℂ).im)).filter
      (fun q => xiZeroCopyOrderKey q <
        xiZeroCopyOrderKey (xiOrderedPositiveZeroCopy n))
  let lower : Fin n → ({q : XiZeroCopy // q ∈ P}) := fun j => by
    let jF : Fin F.card := ⟨j, lt_trans j.isLt hnF⟩
    have hjN : jF < iN := by exact_mod_cast j.isLt
    have heLe : @LE.le XiZeroCopy xiZeroCopyLE (e jF).1 (e iN).1 :=
      (e.le_iff_le).2 hjN.le
    have hkeyLe : xiZeroCopyOrderKey (e jF).1 ≤
        xiZeroCopyOrderKey (e iN).1 := xiZeroCopy_le_iff_key_le.mp heLe
    have hvalNe : (e jF).1 ≠ (e iN).1 := by
      intro hval
      have hfin := e.injective (Subtype.ext hval)
      exact hjN.ne hfin
    have hkeyNe : xiZeroCopyOrderKey (e jF).1 ≠
        xiZeroCopyOrderKey (e iN).1 := fun h =>
      hvalNe (xiZeroCopyOrderKey_injective h)
    have hkeyLtRaw : xiZeroCopyOrderKey (e jF).1 <
        xiZeroCopyOrderKey (e iN).1 := lt_of_le_of_ne hkeyLe hkeyNe
    have hkeyLt : xiZeroCopyOrderKey (e jF).1 <
        xiZeroCopyOrderKey (xiOrderedPositiveZeroCopy n) := by
      rw [← heN]
      exact hkeyLtRaw
    refine ⟨(e jF).1, ?_⟩
    change (e jF).1 ∈ (xiCopiesPos
      (((xiOrderedPositiveZeroCopy n).1 : ℂ).im)).filter
        (fun q => xiZeroCopyOrderKey q <
          xiZeroCopyOrderKey (xiOrderedPositiveZeroCopy n))
    rw [Finset.mem_filter]
    refine ⟨?_, hkeyLt⟩
    have heMem : (e jF).1 ∈ F := (e jF).2
    simpa [F, xiOrderedPositiveZeroCopy_im_eq n] using heMem
  have hlowerInjective : Function.Injective lower := by
    intro j k hjk
    have hval := congrArg Subtype.val hjk
    dsimp [lower] at hval
    have hfin := e.injective (Subtype.ext hval)
    apply Fin.ext
    simpa using congrArg Fin.val hfin
  have hlowerSurjective : Function.Surjective lower := by
    intro x
    have hxP : x.1 ∈ P := x.2
    change x.1 ∈ (xiCopiesPos
      (((xiOrderedPositiveZeroCopy n).1 : ℂ).im)).filter
        (fun q => xiZeroCopyOrderKey q <
          xiZeroCopyOrderKey (xiOrderedPositiveZeroCopy n)) at hxP
    rw [Finset.mem_filter] at hxP
    have hxF : x.1 ∈ F := by
      simpa [F, xiOrderedPositiveZeroCopy_im_eq n] using hxP.1
    let xF : ↑F := ⟨x.1, hxF⟩
    let jF : Fin F.card := e.symm xF
    have hxLe : @LE.le XiZeroCopy xiZeroCopyLE x.1 (e iN).1 := by
      apply xiZeroCopy_le_iff_key_le.mpr
      exact (by simpa [heN] using hxP.2.le)
    have hxFLe : xF ≤ e iN := by exact hxLe
    have hjLe : jF ≤ iN := by
      apply (e.le_iff_le).mp
      simpa [jF] using hxFLe
    have hjNe : jF ≠ iN := by
      intro hEq
      change e.symm xF = iN at hEq
      have hxEq : x.1 = (e iN).1 := by
        have := congrArg Subtype.val (e.apply_symm_apply xF)
        rw [hEq] at this
        exact this.symm
      have : xiZeroCopyOrderKey x.1 < xiZeroCopyOrderKey x.1 := by
        simpa [heN, hxEq] using hxP.2
      exact (lt_irrefl _ this)
    have hjLt : jF < iN := lt_of_le_of_ne hjLe hjNe
    let j : Fin n := ⟨jF, by exact_mod_cast hjLt⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    dsimp [lower, j]
    exact congrArg Subtype.val (e.apply_symm_apply xF)
  have hcard : Fintype.card (Fin n) =
      Fintype.card ({q : XiZeroCopy // q ∈ P}) :=
    Fintype.card_congr (Equiv.ofBijective lower
      ⟨hlowerInjective, hlowerSurjective⟩)
  change P.card = n
  simpa using hcard.symm

abbrev XiPositiveZeroCopy :=
  {q : XiZeroCopy // 0 < (q.1 : ℂ).im}

def xiOrderedPositiveZeroCopyMap (n : ℕ) : XiPositiveZeroCopy :=
  ⟨xiOrderedPositiveZeroCopy n, by
    rw [xiOrderedPositiveZeroCopy_im_eq]
    exact xiOrderedPositiveOrdinate_pos n⟩

theorem xiOrderedPositiveZeroCopyMap_injective :
    Function.Injective xiOrderedPositiveZeroCopyMap := by
  intro n m h
  have hval : xiOrderedPositiveZeroCopy n = xiOrderedPositiveZeroCopy m :=
    congrArg Subtype.val h
  have hrank := congrArg xiPositiveZeroCopyRank hval
  simpa [xiPositiveZeroCopyRank_ordered] using hrank

theorem xiOrderedPositiveZeroCopyMap_surjective :
    Function.Surjective xiOrderedPositiveZeroCopyMap := by
  intro q
  set n : ℕ := xiPositiveZeroCopyRank q.1 with hn
  have hqnPos : 0 < ((xiOrderedPositiveZeroCopy n).1 : ℂ).im := by
    rw [xiOrderedPositiveZeroCopy_im_eq]
    exact xiOrderedPositiveOrdinate_pos n
  have hrankEq : xiPositiveZeroCopyRank (xiOrderedPositiveZeroCopy n) =
      xiPositiveZeroCopyRank q.1 := by
    rw [xiPositiveZeroCopyRank_ordered, ← hn]
  have hkeyEq : xiZeroCopyOrderKey (xiOrderedPositiveZeroCopy n) =
      xiZeroCopyOrderKey q.1 := by
    rcases lt_trichotomy (xiZeroCopyOrderKey (xiOrderedPositiveZeroCopy n))
      (xiZeroCopyOrderKey q.1) with hlt | heq | hgt
    · have hrankLt := xiPositiveZeroCopyRank_lt_of_key_lt hqnPos hlt
      linarith
    · exact heq
    · have hrankLt := xiPositiveZeroCopyRank_lt_of_key_lt q.2 hgt
      linarith
  refine ⟨n, Subtype.ext ?_⟩
  exact xiZeroCopyOrderKey_injective hkeyEq

def xiOrderedPositiveZeroCopyEquiv : ℕ ≃ XiPositiveZeroCopy :=
  Equiv.ofBijective xiOrderedPositiveZeroCopyMap
    ⟨xiOrderedPositiveZeroCopyMap_injective,
      xiOrderedPositiveZeroCopyMap_surjective⟩

theorem xiOrderedPositiveZeroCopyEquiv_im (n : ℕ) :
    ((((xiOrderedPositiveZeroCopyEquiv n).1).1 : XiDivisorSupport) : ℂ).im =
      xiOrderedPositiveOrdinate n := by
  exact xiOrderedPositiveZeroCopy_im_eq n

theorem xiZeroCopyConjEquiv_im (q : XiZeroCopy) :
    (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ).im =
      -((q.1 : ℂ).im) := by
  change ((starRingEnd ℂ) (q.1 : ℂ)).im = -((q.1 : ℂ).im)
  simp

def xiSignedPositiveZeroCopyMap :
    Sum XiPositiveZeroCopy XiPositiveZeroCopy → XiZeroCopy
  | Sum.inl q => q.1
  | Sum.inr q => xiZeroCopyConjEquiv q.1

theorem xiSignedPositiveZeroCopyMap_injective :
    Function.Injective xiSignedPositiveZeroCopyMap := by
  intro q r h
  cases q with
  | inl q =>
      cases r with
      | inl r =>
          congr 1
          exact Subtype.ext h
      | inr r =>
          have him := congrArg (fun s : XiZeroCopy => ((s.1 : ℂ).im)) h
          change (q.1.1 : ℂ).im =
            ((xiZeroCopyConjEquiv r.1).1 : ℂ).im at him
          rw [xiZeroCopyConjEquiv_im] at him
          exfalso
          linarith [q.2, r.2]
  | inr q =>
      cases r with
      | inl r =>
          have him := congrArg (fun s : XiZeroCopy => ((s.1 : ℂ).im)) h
          change ((xiZeroCopyConjEquiv q.1).1 : ℂ).im =
            (r.1.1 : ℂ).im at him
          rw [xiZeroCopyConjEquiv_im] at him
          exfalso
          linarith [q.2, r.2]
      | inr r =>
          congr 1
          apply Subtype.ext
          exact xiZeroCopyConjEquiv.injective h

theorem xiSignedPositiveZeroCopyMap_surjective :
    Function.Surjective xiSignedPositiveZeroCopyMap := by
  intro q
  by_cases hq : 0 < (q.1 : ℂ).im
  · exact ⟨Sum.inl ⟨q, hq⟩, rfl⟩
  · have hqneg : (q.1 : ℂ).im < 0 := by
      have hne := xiSupport_im_ne_zero q.1
      exact lt_of_le_of_ne (le_of_not_gt hq) hne
    let qpos : XiPositiveZeroCopy := ⟨xiZeroCopyConjEquiv q, by
      rw [xiZeroCopyConjEquiv_im]
      linarith⟩
    refine ⟨Sum.inr qpos, ?_⟩
    exact xiZeroCopyConjEquiv_apply_apply q

def xiSignedPositiveZeroCopyEquiv :
    Sum XiPositiveZeroCopy XiPositiveZeroCopy ≃ XiZeroCopy :=
  Equiv.ofBijective xiSignedPositiveZeroCopyMap
    ⟨xiSignedPositiveZeroCopyMap_injective,
      xiSignedPositiveZeroCopyMap_surjective⟩

def xiOrderedSignedZeroCopyEquiv : Sum ℕ ℕ ≃ XiZeroCopy :=
  (Equiv.sumCongr xiOrderedPositiveZeroCopyEquiv
    xiOrderedPositiveZeroCopyEquiv).trans xiSignedPositiveZeroCopyEquiv

def xiOrderedSignedPrimeZeroCopyEquiv :
    RouteKSignedPrimeIndex ≃ XiZeroCopy :=
  (Equiv.sumCongr nthPrimeEquiv.symm nthPrimeEquiv.symm).trans
    xiOrderedSignedZeroCopyEquiv

theorem xiSpectralPoint_orderedPositive_eq_of_rh
    (hRH : RiemannHypothesis) (n : ℕ) :
    xiSpectralPoint (xiOrderedPositiveZeroCopyEquiv n).1 =
      (xiOrderedPositiveOrdinate n : ℂ) := by
  apply Complex.ext
  · simp [xiSpectralPoint, xiOrderedPositiveZeroCopyEquiv_im]
  · simp [xiSpectralPoint,
      xi_divisor_support_re_eq_half_of_rh hRH]

theorem xiSpectralPoint_orderedSignedPrimeZeroCopyEquiv_eq_of_rh
    (hRH : RiemannHypothesis) (i : RouteKSignedPrimeIndex) :
    xiSpectralPoint (xiOrderedSignedPrimeZeroCopyEquiv i) =
      (xiOrderedSignedPrimeMultiplier i)⁻¹ := by
  cases i with
  | inl p =>
      have hpIndex : nthPrimeEquiv.symm p = routeKPrimeRVMIndex p := rfl
      change xiSpectralPoint
          (xiOrderedPositiveZeroCopyEquiv (nthPrimeEquiv.symm p)).1 =
        ((xiOrderedPrimeReciprocal p : ℂ))⁻¹
      rw [xiSpectralPoint_orderedPositive_eq_of_rh hRH, hpIndex,
        xiOrderedPrimeReciprocal]
      norm_cast
      exact (inv_inv _).symm
  | inr p =>
      have hpIndex : nthPrimeEquiv.symm p = routeKPrimeRVMIndex p := rfl
      change xiSpectralPoint
          (xiZeroCopyConjEquiv
            (xiOrderedPositiveZeroCopyEquiv (nthPrimeEquiv.symm p)).1) =
        (-(xiOrderedPrimeReciprocal p : ℂ))⁻¹
      apply Complex.ext
      · rw [xiSpectralPoint]
        simp [xiZeroCopyConjEquiv_im,
          xiOrderedPositiveZeroCopyEquiv_im, hpIndex,
          xiOrderedPrimeReciprocal]
      · simp [xiSpectralPoint,
          xi_divisor_support_re_eq_half_of_rh hRH]

end

end RHTower
