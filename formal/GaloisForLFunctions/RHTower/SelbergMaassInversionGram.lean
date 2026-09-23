import GaloisForLFunctions.RHTower.SelbergMaassCharacterFourier
import GaloisForLFunctions.HTGeometry.FiniteUnipotentFibres

/-!
# Exact arithmetic Gram kernel of the original inversion transfer

The original transfer Gram operator is the upper–lower–upper character average.
Every parameter collision is classified by the annihilator of the middle residue;
the character phase is constant on the entire fibre. Exact finite aggregation gives
the actual convolution kernel, its support, sharp magnitude, and diagonal value.
Its absolute weights are independent of the characters and sum to one. The original
Maass physical lower-channel mass is its literal coefficient Gram energy.
-/

open Complex Set UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassInversionGram
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open GaloisForLFunctions.HTGeometry FiniteRingSl2 FiniteUnipotentFibres
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- The actual positive Gram operator of the finite inversion transfer. -/
def transferGram (N : ℕ) (r s : ZMod (N+1)) :
    EuclideanSpace ℂ (Deck N) →ₗ[ℂ] EuclideanSpace ℂ (Deck N) :=
  (characterProjection N (upperBlock N) s).comp
    ((characterProjection N (lowerBlock N) (-r)).comp
      (characterProjection N (upperBlock N) s))

/-- The inverse of the actual regular unitary is its inverse group motion. -/
theorem regularUnitary_symm (N : ℕ) (g : Deck N) (v : EuclideanSpace ℂ (Deck N)) :
    (finiteRegularUnitary g).symm v=finiteRegularUnitary g⁻¹ v := by
  apply (finiteRegularUnitary g).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext q
  change v q=v ((q*g)*g⁻¹)
  rw [mul_assoc,mul_inv_cancel,mul_one]

/-- The actual Gram form is precisely the squared inversion-transfer norm. -/
theorem transferGram_inner (N : ℕ) (r s : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) :
    (inner ℂ (transferGram N r s v) v).re=‖inversionTransfer N r s v‖^(2 : ℕ) := by
  unfold transferGram
  simp only [LinearMap.comp_apply]
  rw [characterProjection_self_adjoint,characterProjection_lower_conjugate,neg_neg,
    LinearIsometryEquiv.inner_map_eq_flip,regularUnitary_symm]
  simp only [← QuotientGroup.mk_inv]
  rw [characterProjection_inner_left]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- The actual character projector in additive residue coordinates. -/
theorem projection_coord_add (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) (q : Deck N) :
    characterProjection N p r v q=((N+1 : ℕ) : ℂ)⁻¹ *
      ∑ j : ZMod (N+1), (starRingEnd ℂ) (ZMod.stdAddChar (r*j))*v (q*p (Multiplicative.ofAdd j)) := by
  rw [characterProjection_coord]
  congr 1
  exact (Equiv.sum_comp (Multiplicative.ofAdd : ZMod (N+1) ≃ Multiplicative (ZMod (N+1)))
    (fun j : Multiplicative (ZMod (N+1)) =>
      (starRingEnd ℂ) (residueCharacter N r j)*v (q*p j))).symm

/-- The literal three-block word in the actual congruence deck group. -/
def deckTriple (N : ℕ) (a b c : ZMod (N+1)) : Deck N :=
  upperBlock N (Multiplicative.ofAdd a)*lowerBlock N (Multiplicative.ofAdd b)*
    upperBlock N (Multiplicative.ofAdd c)

/-- The exact arithmetic phase of the original Gram word. -/
def tripleWeight (N : ℕ) (r s a b c : ZMod (N+1)) : ℂ :=
  ZMod.stdAddChar (r*b-s*(a+c))

/-- The three original character weights combine to the middle parameter and conserved outer sum. -/
theorem tripleWeight_eq (N : ℕ) (r s a b c : ZMod (N+1)) :
    tripleWeight N r s a b c =
      (starRingEnd ℂ) (ZMod.stdAddChar (s*a))*
        (starRingEnd ℂ) (ZMod.stdAddChar ((-r)*b))*
          (starRingEnd ℂ) (ZMod.stdAddChar (s*c)) := by
  unfold tripleWeight
  simp_rw [← AddChar.inv_apply_eq_conj,← AddChar.map_neg_eq_inv,← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The actual original Gram operator is its complete three-parameter character kernel. -/
theorem transferGram_coord (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) (q : Deck N) :
    transferGram N r s v q=(((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
      ∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
        tripleWeight N r s a b c*v (q*deckTriple N a b c) := by
  unfold transferGram
  simp only [LinearMap.comp_apply]
  simp_rw [projection_coord_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [tripleWeight_eq]
  simp only [deckTriple,mul_assoc]
  ring

/-- The actual deck word reduces to the literal determinant-one matrix word. -/
theorem deckTriple_reduce (N : ℕ) (a b c : ZMod (N+1)) :
    deckResidueEquiv N (deckTriple N a b c)=triple a b c := by
  simp only [deckTriple,map_mul,upperBlock,lowerBlock,MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply,upperHom,lowerHom,
    MonoidHom.coe_mk,OneHom.coe_mk,toAdd_ofAdd]
  rfl

/-- Original deck collisions have the complete annihilator classification. -/
theorem deckTriple_collision (N : ℕ) (a b c a' c' : ZMod (N+1)) :
    deckTriple N a' b c'=deckTriple N a b c ↔ b*(a'-a)=0 ∧ a'+c'=a+c := by
  rw [← (deckResidueEquiv N).injective.eq_iff,deckTriple_reduce,deckTriple_reduce]
  exact triple_collision a b c a' c'

/-- The original character phase is constant on every actual collision fibre. -/
theorem tripleWeight_collision (N : ℕ) (r s a b c a' c' : ZMod (N+1))
    (h : deckTriple N a' b c'=deckTriple N a b c) :
    tripleWeight N r s a' b c'=tripleWeight N r s a b c := by
  unfold tripleWeight
  rw [((deckTriple_collision N a b c a' c').mp h).2]

/-- The complete character weight in one actual deck fibre at fixed middle residue. -/
def fibreWeight (N : ℕ) (r s b : ZMod (N+1)) (g : Deck N) : ℂ := by
  classical
  exact ∑ u : {u : ZMod (N+1)×ZMod (N+1) // deckTriple N u.1 b u.2=g},
    tripleWeight N r s u.1.1 b u.1.2

/-- The normalized original Gram convolution kernel, with every arithmetic fibre retained. -/
def gramKernel (N : ℕ) (r s : ZMod (N+1)) (g : Deck N) : ℂ :=
  (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) * ∑ b : ZMod (N+1), fibreWeight N r s b g

/-- The actual deck-parameter fibre is explicitly the middle-residue annihilator. -/
def deckFibreEquiv (N : ℕ) (a b c : ZMod (N+1)) :
    {t : ZMod (N+1) // b*t=0} ≃
      {u : ZMod (N+1)×ZMod (N+1) // deckTriple N u.1 b u.2=deckTriple N a b c} :=
  (fibreEquiv a b c).trans (Equiv.subtypeEquivRight (fun u => by
    rw [triple_collision,deckTriple_collision]))

/-- Exact phase-coherent aggregation over every original nonunit fibre. -/
theorem fibreWeight_at_word (N : ℕ) (r s a b c : ZMod (N+1)) :
    fibreWeight N r s b (deckTriple N a b c) =
      (Nat.card {t : ZMod (N+1) // b*t=0} : ℂ)*tripleWeight N r s a b c := by
  classical
  unfold fibreWeight
  have he (u : {u : ZMod (N+1)×ZMod (N+1) // deckTriple N u.1 b u.2=deckTriple N a b c}) :
      tripleWeight N r s u.1.1 b u.1.2=tripleWeight N r s a b c :=
    tripleWeight_collision N r s a b c u.1.1 u.1.2 u.2
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    ← Nat.card_congr (deckFibreEquiv N a b c)]

/-- Finite disintegration by the actual deck word retains the complete weighted source sum. -/
theorem fibreWeight_convolution (N : ℕ) (r s b : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) (q : Deck N) :
    (∑ g : Deck N, fibreWeight N r s b g*v (q*g)) =
      ∑ u : ZMod (N+1)×ZMod (N+1),
        tripleWeight N r s u.1 b u.2*v (q*deckTriple N u.1 b u.2) := by
  classical
  have h := Fintype.sum_fiberwise
    (fun u : ZMod (N+1)×ZMod (N+1) => deckTriple N u.1 b u.2)
    (fun u : ZMod (N+1)×ZMod (N+1) =>
      tripleWeight N r s u.1 b u.2*v (q*deckTriple N u.1 b u.2))
  rw [← h]
  apply Finset.sum_congr rfl
  intro g _
  unfold fibreWeight
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [u.2]

/-- The constructed kernel is the literal convolution kernel of the original Gram operator. -/
theorem transferGram_convolution (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) (q : Deck N) :
    transferGram N r s v q=∑ g : Deck N, gramKernel N r s g*v (q*g) := by
  classical
  rw [transferGram_coord]
  calc
    _ = (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
      ∑ b : ZMod (N+1), ∑ a : ZMod (N+1), ∑ c : ZMod (N+1),
        tripleWeight N r s a b c*v (q*deckTriple N a b c) := by
          congr 1
          exact Finset.sum_comm
    _ = (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
      ∑ b : ZMod (N+1), ∑ g : Deck N, fibreWeight N r s b g*v (q*g) := by
          congr 1
          apply Finset.sum_congr rfl
          intro b _
          rw [fibreWeight_convolution,Fintype.sum_prod_type]
    _ = (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
      ∑ g : Deck N, ∑ b : ZMod (N+1), fibreWeight N r s b g*v (q*g) := by
          congr 1
          exact Finset.sum_comm
    _ = _ := by
      unfold gramKernel
      simp_rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- The actual matrix lower entry determines the only possible middle residue. -/
theorem fibreWeight_eq_zero_of_lowerEntry_ne (N : ℕ) (r s b : ZMod (N+1))
    (g : Deck N) (hb : deckResidueEquiv N g 1 0≠b) : fibreWeight N r s b g=0 := by
  classical
  haveI : IsEmpty {u : ZMod (N+1)×ZMod (N+1) // deckTriple N u.1 b u.2=g} := by
    constructor
    intro u
    have h := congrArg (fun g : Deck N => deckResidueEquiv N g 1 0) u.2
    rw [deckTriple_reduce,triple_entry10] at h
    exact hb h.symm
  simp [fibreWeight]

/-- The complete kernel value is its annihilator multiplicity times the exact arithmetic phase. -/
theorem gramKernel_at_word (N : ℕ) (r s a b c : ZMod (N+1)) :
    gramKernel N r s (deckTriple N a b c) =
      (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
        ((Nat.card {t : ZMod (N+1) // b*t=0} : ℂ)*tripleWeight N r s a b c) := by
  classical
  unfold gramKernel
  congr 1
  rw [Finset.sum_eq_single b,fibreWeight_at_word]
  · intro b' _ hne
    apply fibreWeight_eq_zero_of_lowerEntry_ne
    rw [deckTriple_reduce,triple_entry10]
    exact Ne.symm hne
  · simp

/-- The neutral three-factor word is the identity of the actual deck group. -/
theorem deckTriple_zero (N : ℕ) : deckTriple N 0 0 0=1 := by
  unfold deckTriple
  change upperBlock N 1*lowerBlock N 1*upperBlock N 1=1
  simp

/-- The original Gram kernel has exact diagonal value one over level squared. -/
theorem gramKernel_one (N : ℕ) (r s : ZMod (N+1)) :
    gramKernel N r s 1=(((N+1 : ℕ) : ℂ)⁻¹)^(2 : ℕ) := by
  classical
  rw [← deckTriple_zero N,gramKernel_at_word]
  have hc : Nat.card {t : ZMod (N+1) // (0 : ZMod (N+1))*t=0}=N+1 := by
    simp [Nat.card_eq_fintype_card]
  rw [hc]
  simp only [tripleWeight,mul_zero,zero_add,sub_zero,AddChar.map_zero_eq_one,mul_one]
  have hN : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  field_simp

open SelbergMaassMean SelbergMaassUnipotentFourier MeasureTheory

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Original physical lower-channel mass is the convergent sum of its actual coefficient Gram forms. -/
theorem source_lower_gram_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ =>
      (inner ℂ (transferGram N (-r) (n : ZMod (N+1)) (coefficientVector N f n y))
        (coefficientVector N f n y)).re)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖characterProjection N (lowerBlock N) r
          (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ)) := by
  simp_rw [transferGram_inner]
  exact lowerCharacter_transfer_hasSum N f r hy

/-- Every original three-factor arithmetic phase has modulus one. -/
theorem tripleWeight_norm (N : ℕ) (r s a b c : ZMod (N+1)) :
    ‖tripleWeight N r s a b c‖=1 := by
  unfold tripleWeight
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle (r*b-s*(a+c))).norm_coe

/-- Sharp kernel magnitude at every admissible word, including composite-level nonunits. -/
theorem gramKernel_at_word_norm (N : ℕ) (r s a b c : ZMod (N+1)) :
    ‖gramKernel N r s (deckTriple N a b c)‖=
      (((N+1 : ℕ) : ℝ)⁻¹)^(3 : ℕ) * (Nat.card {t : ZMod (N+1) // b*t=0} : ℝ) := by
  rw [gramKernel_at_word,norm_mul,norm_pow,norm_inv,norm_mul,tripleWeight_norm]
  simp only [Complex.norm_natCast,mul_one]

/-- Every admissible three-factor word contributes nonzero original kernel weight. -/
theorem gramKernel_at_word_ne_zero (N : ℕ) (r s a b c : ZMod (N+1)) :
    gramKernel N r s (deckTriple N a b c)≠0 := by
  classical
  letI : Nonempty {t : ZMod (N+1) // b*t=0} := ⟨⟨0,mul_zero b⟩⟩
  have hN : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  have hc : (Nat.card {t : ZMod (N+1) // b*t=0} : ℂ)≠0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have hp : tripleWeight N r s a b c≠0 := by
    intro hz
    have h := tripleWeight_norm N r s a b c
    rw [hz,norm_zero] at h
    exact zero_ne_one h
  rw [gramKernel_at_word]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hN)) (mul_ne_zero hc hp)

/-- The exact support of the original Gram kernel is the image of its three-factor map. -/
theorem gramKernel_ne_zero_iff (N : ℕ) (r s : ZMod (N+1)) (g : Deck N) :
    gramKernel N r s g≠0 ↔ ∃ a b c : ZMod (N+1), g=deckTriple N a b c := by
  classical
  constructor
  · intro h
    by_contra hx
    have he (b : ZMod (N+1)) : fibreWeight N r s b g=0 := by
      haveI : IsEmpty {u : ZMod (N+1)×ZMod (N+1) // deckTriple N u.1 b u.2=g} := by
        constructor
        intro u
        exact hx ⟨u.1.1,b,u.1.2,u.2.symm⟩
      simp [fibreWeight]
    apply h
    simp [gramKernel,he]
  · rintro ⟨a,b,c,rfl⟩
    exact gramKernel_at_word_ne_zero N r s a b c

/-- The original neutral Gram kernel has total mass one. -/
theorem sum_neutral_gramKernel (N : ℕ) : (∑ g : Deck N, gramKernel N 0 0 g)=1 := by
  classical
  let v : EuclideanSpace ℂ (Deck N) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have h := transferGram_convolution N 0 0 v 1
  have he : (∑ g : Deck N, gramKernel N 0 0 g)=transferGram N 0 0 v 1 := by
    simpa only [v,WithLp.ofLp_toLp,one_mul,mul_one] using h.symm
  rw [he,transferGram_coord]
  change (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
    (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1), tripleWeight N 0 0 a b c*1)=1
  simp only [tripleWeight,zero_mul,sub_zero,AddChar.map_zero_eq_one,mul_one,
    Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have hN : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  field_simp

/-- All character pairs have exactly the same absolute kernel as the neutral pair. -/
theorem neutral_gramKernel_eq_norm (N : ℕ) (r s : ZMod (N+1)) (g : Deck N) :
    gramKernel N 0 0 g=(‖gramKernel N r s g‖ : ℂ) := by
  classical
  by_cases hx : ∃ a b c : ZMod (N+1), g=deckTriple N a b c
  · obtain ⟨a,b,c,rfl⟩ := hx
    rw [gramKernel_at_word,gramKernel_at_word_norm]
    simp [tripleWeight]
  · have hn (u v : ZMod (N+1)) : gramKernel N u v g=0 := by
      by_contra h
      exact hx ((gramKernel_ne_zero_iff N u v g).mp h)
    simp [hn]

/-- The absolute original arithmetic Gram kernel is an exact probability distribution. -/
theorem sum_norm_gramKernel (N : ℕ) (r s : ZMod (N+1)) :
    (∑ g : Deck N, ‖gramKernel N r s g‖)=1 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← neutral_gramKernel_eq_norm]
  exact sum_neutral_gramKernel N

end
end GaloisForLFunctions.RHTower.SelbergMaassInversionGram
