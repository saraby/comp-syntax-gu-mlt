--# -path=.:../abstract
concrete MicroLangAra of MicroLang = open MicroResAra, Prelude in {

-----------------------------------------------------
---------------- Grammar part -----------------------
-----------------------------------------------------

  lincat
  
    Utt = {s : Str};

    S  = {s : Str} ; -- subordinate clause has nominal word order and subject in acc
    VP = {verb : Verb ; compl : AgreementGNSp => Str} ;    -- verb phrase                         e.g. "lives here"
    Comp = {s : AgreementGNSp => Str} ;
    AP = Adjective;
    N, CN = Noun;
    NP = {s : Case => Str ; a : AgreementGNSp ; isPron : Bool} ;
    Pron = {s : Case => Str ; a : AgreementGNSp ; isPron : Bool };
    Det = {s : Str ; st : State ; n : Number } ;
    Prep = {s : Str} ;
    V = Verb ;
    V2 = Verb2 ;
    A = Adjective ;
    -- N = Noun ;
    Adv = {s : Str} ;

  lin
    UttS s = s ;
    UttNP np = {s = np.s ! Nom} ;

    PredVPS np vp = {
      s = np.s ! Nom ++ vp.verb.s ! Impf ! np.a  ++ vp.compl ! np.a
      } ;
      
    UseV v = {
      verb = v ;
      compl = \\_ => "" 
      } ;
      
    ComplV2 v2 np = case np.isPron of {
      True  => {verb = {s = \\t,a => v2.s ! t ! a ++ BIND ++ np.s ! Acc} ;compl = \\_ => "" } ;
      False => {verb = v2 ; compl=\\a=> v2.c ++ (np.s ! Acc) }
    } ;
      
    UseComp comp = {
      verb = be_Verb;   -- the verb is the copula "be"
      compl = \\a => comp.s ! a
      } ;
      
    CompAP ap = {s = \\agr => ap.s ! Indef ! agr ! Nom} ;
      
    AdvVP vp adv =
      vp ** {compl = \\a => vp.compl ! a ++ adv.s} ;
      
    DetCN det cn = {
      s  = \\c => cn.s ! det.st ! det.n ! c;
      a  = AgrGNSp cn.g det.n cn.sp;
      isPron = False
      } ;
      
    UsePron p = {
      s = \\c => p.s ! c ;
      a = p.a ;
      isPron = True 
    };
            
    a_Det     = {s = "" ; st=Indef ; n= Sg } ;
    aPl_Det   = {s = "" ; st=Indef ; n= (Dl | Pl) } ;
    the_Det   = {s = "" ; st=Def   ; n= Sg } ;
    thePl_Det = {s = "" ; st=Def   ; n= (Dl | Pl) } ;
    
    UseN n = n ;
    
    AdjCN ap cn = {
      s  = \\st,n,c => cn.s ! st ! n ! c ++ ap.s ! st ! AgrGNSp cn.g n cn.sp ! c  ;
      g  = cn.g;
      sp = cn.sp ;
      } ;

    PositA a = a ;

    PrepNP prep np = case np.isPron of { 
      True  => { s = prep.s ++ BIND ++(np.s ! Acc) ; a = np.a} ;
      False => { s = prep.s ++ np.s ! Acc ; a = np.a }
    };

    in_Prep = {s = "في"} ;
    on_Prep = {s = "على"} ;
    with_Prep = {s = "مع"} ;

    he_Pron = {
      s = table {Nom => "هو" ; Acc => "ه"} ;
      a = (AgrGNSp Masc Sg Hum | AgrGNSp Masc Sg NoHum ) ; 
      isPron = True
      } ;
    she_Pron = {
      s = table {Nom => "هي" ; Acc => "ها"} ;
      a = (AgrGNSp Fem Sg Hum | AgrGNSp Fem Sg NoHum );
      isPron = True
      } ;
    they_Pron = {
      s = table {Nom => "هم" ; Acc => "هم"} ;
      a = AgrGNSp Masc Pl Hum;
      isPron = True
      } ;

    

-----------------------------------------------------
---------------- Lexicon part -----------------------
-----------------------------------------------------

------------Adverbs-------------

    lin already_Adv = mkAdv "مسبقًا" ;
    lin now_Adv = mkAdv "الآن"| mkAdv "حاليًا" ;

------------Nouns--------------
   ---------Masc-----------
    lin animal_N = mkN "حيوان" "حيوانات" Masc Hum ;
    lin baby_N = mkN "رضيع" "رضع" Masc Hum ;
    lin boy_N = mkN "صبي" "صبية" Masc Hum ;
    lin friend_N = mkN "صديق" "أصدقاء" Masc Hum ;
    lin man_N = mkN "رجل" "رجال" Masc Hum ;
    lin child_N = mkN "طفل" "أطفال" Masc Hum ;

    lin bird_N = mkN "طير" "طيور" Masc NoHum ;
    lin boat_N = mkN "قارب" "قوارب" Masc NoHum ;
    lin book_N = mkN "كتاب" "كتب" Masc NoHum ;
    lin computer_N = mkN "حاسوب" "حواسيب" Masc NoHum;
    lin dog_N = mkN "كلب" "كلاب" Masc NoHum ;
    lin horse_N = mkN "حصان" "أحصنة" Masc NoHum ;
    lin house_N = mkN "بيت" "بيوت" Masc NoHum ;
    lin train_N = mkN "قطار" "قطارات" Masc NoHum ;
    lin river_N = mkN "نهر" "أنهار" Masc NoHum ;
    lin sea_N = mkN "بحر" "بحار" Masc NoHum ;
      -------NoDl-------
    lin water_N = mkN "ماء" "مياه" Masc NoHum ;
    lin blood_N = mkN "دم" "دماء" Masc NoHum ;
   ----------Fem-----------
    lin apple_N = mkN "تفاحة" Fem NoHum ;
    lin bike_N = mkN "دراجة" Fem NoHum ;
    lin car_N = mkN "سيارة" Fem NoHum ;
    lin cow_N = mkN "بقرة" Fem NoHum ;
    lin fish_N = mkN "سمكة" Fem NoHum ;
    lin flower_N = mkN "زهرة" Fem NoHum ;
    lin girl_N = mkN "بنت" Fem Hum ;
    lin bread_N = mkN "خبزة" Fem NoHum ;
    lin star_N = mkN "نجمة" Fem NoHum ;
    lin tree_N = mkN "شجرة" Fem NoHum ;
    lin language_N = mkN "لغة" Fem NoHum ;

    lin cat_N = mkN "قطة" "قطط" Fem NoHum ;
    lin city_N = mkN "مدينة" "مدن" Fem NoHum ;
    lin cloud_N = mkN "سحابة" "سحب" Fem NoHum ;
    lin woman_N = mkN "امرأة" "نساء" Fem Hum ;
    lin ship_N = mkN "سفينة" "سفن" Fem NoHum ;

      -------NoDl-------
    lin fire_N = mkN "نار" Fem NoHum ;
   ---------NoPl-----------
    lin music_N = mkN "موسيقى" Fem NoHum ;
    lin grammar_N = mkN "قواعد" Fem NoHum ;
    lin beer_N = mkN "جعة" Fem NoHum ;
    lin milk_N = mkN "حليب" Masc NoHum ;
    lin wine_N = mkN "نبيذ" Masc NoHum ;
------------Adjs---------------
    lin white_A = mkA "أبيض" ;
    lin red_A = mkA "أحمر" ;
    lin black_A = mkA "أسود" ;
    lin blue_A = mkA "أزرق" ;
    lin green_A = mkA "أخضر" ;
    lin yellow_A = mkA "أصفر" ;

    lin young_A = mkA "صغير" ;
    lin small_A = mkA "صغير" ;
    lin warm_A = mkA "دافئ" ;
    lin heavy_A = mkA "ثقيل" ;
    lin clean_A = mkA "نظيف" ;
    lin new_A = mkA "جديد" ;
    lin big_A = mkA "كبير" ;
    lin old_A = mkA "قديم" ;

    lin bad_A = mkA "سيء" ;
    lin clever_A = mkA "ذكي" ;
    lin dirty_A = mkA "متسخ" ;
    lin cold_A = mkA "بارد" ;
    lin good_A = mkA "جيد" ;
    lin hot_A = mkA "ساخن" ;
    lin ready_A = mkA "مستعد" ;

------------Verbs--------------
    lin go_V = mkV "ذهب" ;
    lin jump_V = mkV "قفز" ;
    lin travel_V = mkV "سافر" ;
    lin swim_V = mkV "سبح" ;
    lin run_V = mkV "ركض" ;
    lin sleep_V = mkV "نام" "نام" "نمن" ;
    lin play_V = mkV "لعب" ;
    lin come_V = mkV "جاء" ;
    lin live_V = mkV "عاش" "عيش" "عشن";
    lin walk_V = mkV "مشى" ;
   ------Trasitive Verbs-------
    lin drink_V2 = mkV2 (mkV "شرب") ;
    lin eat_V2 = mkV2 (mkV "أكل") ;
    lin kill_V2 = mkV2 (mkV "قتل") ;
    lin understand_V2 = mkV2 (mkV "فهم" ) ;
    lin teach_V2 = mkV2 (mkV "علم" ) ;
    lin read_V2 = mkV2 (mkV "قرأ" ) ;
    lin break_V2 = mkV2 (mkV "كسر") ;
    lin wait_V2 = mkV2 (mkV "انتظر") ;
    lin see_V2 = mkV2 (mkV "رأى" ) ;
    lin find_V2 = mkV2 (mkV "وجد" ) ;
    lin love_V2 = mkV2 (mkV "أحب" "حب" "حببن") ;
    lin buy_V2 = mkV2 (mkV "اشترى") ;
    -- lin john_PN = mkPN "John" ;
    -- lin know_VS = mkVS (mkV "know" "knew" "known") ;
    -- lin paris_PN = mkPN "Paris" ;

    oper

{- The following commented out tries were some failed ones, trying to bind the verb|prep with the accusative case of the pron
 in case it comes after them, but no luck with that, especially with this limited grammar rules I can follow -}


      -- adding a pron to a preposotion 
    -- pronPrepSuff: Str -> Str -> Str
    --   = \prep, pron -> case prep of {
    --     sub + "ى" => sub + "ي" + pron ;
    --     _         => prep + pron
    -- } ;


    -- pronSuff: Str-> Str -> Str
    --   = \v, pron -> case v of {
    --     r + "أى" => r + "آ" + pron ;
    --     sub + "ى" => sub + "ا" + pron ;
    --     _         => v + pron 
    -- } ;

    ---------------------------
    -- Paradigms part ---------
    ---------------------------

    mkN = overload {
      
      mkN : Str -> Gender -> Species -> Noun   -- predictable noun
        = \sg,g,sp -> lin N (femNoun sg g sp) ;
      
      mkN : (sg,pl:Str) -> Gender -> Species -> Noun  -- irregular noun, e.g. man-men
        = \sg,pl,g,sp -> lin N (brokenNoun sg pl g sp) ;
    } ;

    mkV = overload {
      mkV : (past : Str) -> V  -- predictable verb
        = \s -> lin V (weakVerb s) ;
      mkV : (past,pres,femPlRoot : Str) -> V  -- irregular verb
        = \past,pres,femPlRoot -> lin V (specialVerb past pres femPlRoot) ;
    } ;

    mkV2 = overload {
     mkV2 : V -> V2            -- any verb with direct object
        = \v   -> lin V2 (v ** {c = []}) ;
      mkV2 : V -> Str -> V2     -- any verb with preposition (no such case in Arabic of the selected lexicon)
        = \v,p -> lin V2 (v ** {c = p}) ;
      } ;

    mkA : Str -> A
      = \ms -> lin A (mkAdj ms) ;

    mkAdv : Str -> Adv
      = \s -> lin Adv {s = s} ;
      
    mkPrep : Str -> Prep
      = \s -> lin Prep {s = s} ;

}