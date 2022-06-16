concrete DoctorAra of Doctor =
  open
    SyntaxAra,
    ParadigmsAra,
    Prelude
  in {

-- application using standard RGL

lincat
  Phrase = Utt ;
  Fact = Cl ;
  Action = VP ;
  Property = VP ;
  Profession = CN ;
  Person = NP ;
  Place = {at,to : Adv} ;
  Substance = NP ;
  Illness = NP ;

lin
  presPosPhrase fact = mkUtt (mkS fact) ;
  presNegPhrase fact = mkUtt (mkS negativePol fact) ;
  pastPosPhrase fact = mkUtt (mkS anteriorAnt fact) ;
  pastNegPhrase fact = mkUtt (mkS anteriorAnt negativePol fact) ;
  presQuestionPhrase fact = let q : Utt = mkUtt (mkQS (mkQCl fact)) in q ** {s =\\c => q.s ! c ++ SOFT_BIND ++ "؟"} ;
  pastQuestionPhrase fact = let q : Utt = mkUtt (mkQS anteriorAnt (mkQCl fact)) in q ** {s =\\c => q.s ! c ++ SOFT_BIND ++ "؟"} ;

  impPosPhrase action = mkUtt (mkImp action) ;
  impNegPhrase action = mkUtt negativePol (mkImp action) ;

  actionFact person action = mkCl person action ;
  propertyFact person property = mkCl person property ;

  isProfessionProperty profession = mkVP (mkNP a_Det profession) ;
  needProfessionProperty profession = mkVP need_V2 (mkNP a_Det profession) ;
  isAtPlaceProperty place = mkVP place.at ;
  haveIllnessProperty illness = mkVP have_V2 illness ;

  theProfessionPerson profession = mkNP the_Det profession ;

  iMascPerson = i_NP ;
  iFemPerson = i_NP ;
  youMascPerson = you_NP ;
  youFemPerson = you_NP ;
  hePerson = he_NP ;
  shePerson = she_NP ;

  goToAction place = mkVP (mkVP go_V) place.to ;
  stayAtAction place = mkVP (mkVP stay_V) place.at ;
  vaccinateAction person = mkVP vaccinate_V2 person ;
  examineAction person = mkVP examine_V2 person ;
  takeSubstanceAction substance = mkVP take_V2 substance ;

-- end of what could be a functor
--------------------------------

  coughAction = mkVP (mkV "سعل" FormI) ;
  breatheAction = mkVP (mkV "تنفس" FormII ) ;
  vomitAction = mkVP (mkV "تقيأ" FormI) ;
  sleepAction = mkVP (mkV "نام" FormI ) ;
  -- dress and undress actions in Arabic need no prepositions
  undressAction = mkVP (mkV2 (mkV "خلع" FormI)) (mkNP thePl_Det (mkN "ثوب")) ;
  dressAction = mkVP (mkV2 (mkV "لبس" FormI)) (mkNP thePl_Det (mkN "ثوب")) ;
  eatAction = mkVP (mkV "أكل" FormI) ;
  drinkAction = mkVP (mkV "شرب" FormI) ;
  smokeAction = mkVP (mkV "دخن" FormI) ;
  measureTemperatureAction = mkVP (mkV2 (mkV "قاس" FormI)) (mkNP (mkN "درجة حرارة الجسم")) ;
  measureBloodPressureAction = mkVP (mkV2 (mkV "قاس" FormI)) (mkNP (mkN "ضغط الدم")) ;

  hospitalPlace = {at = pAdv "في المستشفى" ; to = pAdv "إلى المستشفى"} ;
  homePlace = {at = pAdv "في المنزل" ; to = pAdv "إلى المنزل"} ;
  schoolPlace = {at = pAdv "في المدرسة" ; to = pAdv "إلى المدرسة"} ;
  workPlace = {at = pAdv "في العمل" ; to = pAdv "إلى العمل"} ;

  doctorProfession = mkCN (mkN "طبيب") ;
  nurseProfession = mkCN (mkN "ممرض") ;
  interpreterProfession = mkCN (mkN "مفسر") ;

  bePregnantProperty = mkVP (mkA "حامل") ;
  beIllProperty = mkVP (mkA "مريض") ;
  beWellProperty = mkVP (mkA "سليم") ;
  beDeadProperty = mkVP (mkA "ميت") ;
  haveAllergiesProperty = mkVP have_V2 (mkNP aPl_Det (mkN "حساسية")) ;
  havePainsProperty = mkVP have_V2 (mkNP aPl_Det (mkN "ألم")) ;
  haveChildrenProperty = mkVP have_V2 (mkNP aPl_Det (mkN "طفل" )) ;

  feverIllness = mkNP a_Det (mkN "حمى") ;
  fluIllness = mkNP a_Det (mkN "زكام") ;
  headacheIllness = mkNP a_Det (mkN "صداع") ;
  diarrheaIllness = mkNP a_Det (mkN "إسهال") ;
  heartDiseaseIllness = mkNP a_Det (mkN "اعتلال قلبي") ;
  lungDiseaseIllness = mkNP a_Det (mkN "مرض رئوي") ;
  hypertensionIllness = mkNP (mkN "ارتفاع ضغط") ;

  alcoholSubstance = mkNP (mkN "كحول") ;
  medicineSubstance = mkNP a_Det (mkN "عقار") ;
  drugsSubstance = mkNP aPl_Det (mkN "مخدر") ;

oper
  pAdv : Str -> Adv = ParadigmsAra.mkAdv ;

  go_V = mkV "ذهب" FormI ;
  stay_V = mkV "بقي" FormIV ;
  need_V2 = mkV2 (mkV "احتاج" FormI) ;
  take_V2 = mkV2 (mkV "أخذ" FormI) ;
  put_V2 = mkV2 (mkV "وضع" FormI ) ;
  vaccinate_V2 = mkV2 (mkV "لقح" FormII) ;
  examine_V2 = mkV2 (mkV "فحص" FormI) ;

}
