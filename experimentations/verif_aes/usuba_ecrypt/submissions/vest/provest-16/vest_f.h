/* VEST core accumulator feedback functions */

static const u32		vest_f[1024][vest_f_words] =
{
	{0xDA46704F}, {0x41F68DE1}, {0x265DE859}, {0x892FCC1E}, {0xBA526D26}, {0xA96B11BC}, {0x9CE447C6}, {0xA265B61E},
	{0x4790CDB6}, {0x10F8DF1C}, {0xC47CD24B}, {0x97C62572}, {0x1DC65D25}, {0x38BC364B}, {0x89F83336}, {0xA7654CB4},
	{0x631BCA96}, {0x636A4BC3}, {0x574C85DC}, {0xC7052AEE}, {0x3539E70C}, {0x13BFC18A}, {0x3D5152D9}, {0x72F5412E},
	{0xA1FE2385}, {0x3B6153AA}, {0xB4625F25}, {0x512AEE36}, {0x9A8E18AF}, {0x07C4CFC6}, {0x9B259B4A}, {0x3E0E6276},
	{0x64A73A96}, {0x19B66B23}, {0xD7402DBC}, {0x85E23E36}, {0x9F22D19A}, {0x9F1530BC}, {0x23F15DC2}, {0xC0733AE6},
	{0xB071ADA6}, {0xB69D1C94}, {0xA42BB656}, {0x9C31A9CE}, {0x972F8B21}, {0x4D2B6C2E}, {0x838F74A6}, {0xB9255798},
	{0x2E9A0DD6}, {0x34F43633}, {0xF44C342F}, {0x92E31A5E}, {0x894CBEA5}, {0x95A83C3B}, {0xB62F8469}, {0xA87F05A6},
	{0x7109AF9A}, {0x92D3BA94}, {0x0DEF20E6}, {0xF23329B4}, {0x72664B2E}, {0x2A732E8E}, {0x34D5D496}, {0x5B237265},
	{0x8D229CF6}, {0xC7660DA5}, {0x8C0BE772}, {0xB96D518C}, {0x356FA232}, {0x8FD16496}, {0x4C5D59E4}, {0x52AB627C},
	{0xB27E5065}, {0xCA3B1D26}, {0x9C7431AD}, {0x534EAA36}, {0x5F418EE1}, {0x91A4DF1C}, {0x44E7729C}, {0x351BE0AE},
	{0xB5A3299C}, {0xD543D52C}, {0xD453D8A6}, {0x8A64BF94}, {0x70D6722D}, {0x9BA55166}, {0xA372E643}, {0xC6B81BC6},
	{0x13CBCD58}, {0x36CA437A}, {0xD26A4B36}, {0x8BF25516}, {0x82DA6A9E}, {0x45E18CDE}, {0xBB1C2E43}, {0xC5239AB6},
	{0x446FCE46}, {0x7E271946}, {0x2D726A1E}, {0x9C047BD9}, {0x462ABB2E}, {0x723532D9}, {0x96F709C4}, {0x93258EF2},
	{0xA37A11CE}, {0xC1E629AD}, {0x97893746}, {0xF271133C}, {0x547C95D2}, {0x119AF1D9}, {0x364EC0F5}, {0x6476598E},
	{0x47E20D6D}, {0x867192FA}, {0xC7F42265}, {0x8F5C614B}, {0x4D2BB836}, {0x96D50AE5}, {0x9646C37C}, {0xF1624676},
	{0x90FC8E1B}, {0x9849DACE}, {0x079B9AC3}, {0x12DDCC4E}, {0x993BD416}, {0xF07D189C}, {0x2F2937B0}, {0xD2840FFA},
	{0xA65D4BD0}, {0xF2261C9B}, {0x6179691E}, {0xC1BC705E}, {0xC7E64551}, {0x26C165DE}, {0x9769D522}, {0x39567A49},
	{0x0B98FE85}, {0x0E25F4F4}, {0x24FC6476}, {0x8F813EC9}, {0xDC09759A}, {0xE2336A8E}, {0x9185F1EC}, {0xC5866976},
	{0x8B684BF4}, {0xE55D0D16}, {0xC07A2E5E}, {0x50C37DAC}, {0x4623BF98}, {0xC1B3299E}, {0x94E17F30}, {0xA74F0D1C},
	{0x8BE13AA6}, {0x7334E949}, {0x7B096A69}, {0xA1655BF0}, {0xD0A76A69}, {0x1A3DFC11}, {0x4760F873}, {0x17F3C50A},
	{0x347F82A6}, {0x2EE7191A}, {0x721E43E5}, {0x74956B26}, {0x5330EDC3}, {0x3D0DAC56}, {0xA5478DCC}, {0x328575E9},
	{0x865FA744}, {0xC42D2F6A}, {0xE3256B98}, {0xC42A7B4B}, {0x73865A59}, {0x1F16A1E5}, {0xB75700BC}, {0xB1EB590A},
	{0xA37E8D03}, {0x3E624C3B}, {0x56993E52}, {0xA54566BC}, {0x8F99455A}, {0x6A5A631E}, {0x729945CE}, {0x0CFAA51E},
	{0xD1AA33B1}, {0x712B6A72}, {0x3627A69C}, {0x879B1BA4}, {0x16C2DF46}, {0x51A1D8DE}, {0x47CC709B}, {0x2C7A474D},
	{0x55BD43C4}, {0x1AF22D66}, {0x2B5A4C3B}, {0xCD1A6D19}, {0x2BED1836}, {0x4F5B6252}, {0x25D6D0CB}, {0x94BACB46},
	{0xC07A55E6}, {0x44EB19D6}, {0x8276E1B9}, {0xD525D9D0}, {0x0ED04FDC}, {0x0E9EF825}, {0x1A76E174}, {0xC2539DC6},
	{0xDE053B94}, {0x5A0C2FDA}, {0xA63D4BB0}, {0x4E6F1958}, {0x52B36D64}, {0x21EDB19A}, {0xB05CD6C3}, {0x784D661E},
	{0x1D884DFC}, {0xF06B6552}, {0x9E64897A}, {0xE43F2986}, {0x2352EF45}, {0x9727D30C}, {0x927783AC}, {0x737306C3},
	{0xA53D6652}, {0x61AE69C9}, {0x77905D16}, {0x568D0CFC}, {0xE51D0D9A}, {0x1EB233B4}, {0x186FE272}, {0x4AD5790E},
	{0x4FA419D6}, {0x3E2A4C73}, {0x73A1392E}, {0x857D92C6}, {0xD2AA12AF}, {0xCC615C9E}, {0x26A1B1FC}, {0x741D4BCA},
	{0x2C43E7D4}, {0x77C511D2}, {0x2FF42E03}, {0x2B4D6DC1}, {0x1C6E8B5A}, {0x9813F87A}, {0x4E2EB316}, {0x9D507374},
	{0x507BDA34}, {0x747243E6}, {0x24A63AF5}, {0x9271F4B4}, {0xD7C5170C}, {0xD63489AE}, {0x9B7944D2}, {0x743ACD49},
	{0x2A29F71C}, {0x560FC6B4}, {0x1F8FC11C}, {0x98714F6C}, {0x73376B04}, {0xB833568E}, {0xD7417D12}, {0xA4532FB8},
	{0xA661B1DA}, {0x82E5774C}, {0x2E722B5C}, {0x9757C074}, {0x9F9222E5}, {0xD1643C8F}, {0xE46B09E6}, {0xA25F38C3},
	{0xA74F5066}, {0x4D2854FB}, {0x3B236D38}, {0xBB2311E6}, {0x5258DCA7}, {0x06AFB85C}, {0x1AFD470C}, {0x46D55D8C},
	{0xA531BD46}, {0x9579F01A}, {0xA52A4D6E}, {0x305CD9DA}, {0x99E90CB6}, {0x8497ED52}, {0x1EB720E6}, {0xD42A0FAD},
	{0x85A2BA3E}, {0x897CB0B3}, {0x71B246E5}, {0x1B8B792C}, {0x9551F652}, {0xA61D6BA4}, {0xA6E5631A}, {0xC65ED225},
	{0x4C5D6D58}, {0x9931A96E}, {0xDB507159}, {0xD40DC9BC}, {0x8753B0BA}, {0x2E1EB463}, {0xD6173D50}, {0x9323F07A},
	{0x9501F6CE}, {0xA786703E}, {0x14F990FC}, {0xC7DE01E1}, {0x9381DB6A}, {0xB61381FA}, {0x52FB305C}, {0x1938F52D},
	{0x6149D9DA}, {0xAD3D254C}, {0x082FAAED}, {0xA4D5339C}, {0x36A57646}, {0x534D8CF2}, {0x5F14C8E3}, {0x85498FBA},
	{0xC259AB9C}, {0x879538F4}, {0x6C661D96}, {0xF20E457C}, {0x2FD04D1E}, {0x0D79D459}, {0x4D617BA1}, {0xB073F854},
	{0x1585EF98}, {0x45B06F63}, {0x1A32EB3A}, {0x9CD55616}, {0xD651BC0E}, {0xD0DC583B}, {0x1D884BFA}, {0x871FE446},
	{0xC86913EE}, {0x04B9B2F9}, {0x92B670AD}, {0x279970AE}, {0x94AB8DC6}, {0x13E3C69A}, {0x5365D94C}, {0xC4636EA6},
	{0x1949EED1}, {0x774D13D0}, {0x41DB7C23}, {0xCF184D63}, {0x24CF70F4}, {0x8AEF4A26}, {0x22699DB6}, {0x9853CB5C},
	{0xB526C23E}, {0x7A6246B9}, {0xA49F31A6}, {0x34B371F0}, {0x8D3927A6}, {0x0AC9DB5A}, {0x9C17D49A}, {0x2E4DD31C},
	{0xB403AD6E}, {0x82F72B64}, {0x0DA24EBD}, {0x9918AADD}, {0x5C3A1B9A}, {0x1CF25B52}, {0xAD3B07A4}, {0x228DABF2},
	{0xDD051DCC}, {0x54C74CF4}, {0x1C6EC54E}, {0xB507D3A4}, {0x4D59AD1A}, {0x977489C6}, {0x85A7F485}, {0x31BA43E3},
	{0xA529D23E}, {0xB5239D64}, {0x7218746F}, {0x2765DA34}, {0x4F630ED4}, {0x307DD651}, {0x73BC30A3}, {0x8E39D91A},
	{0xA6756A1A}, {0x0FBD3245}, {0xBF510879}, {0x1AF154CE}, {0x13E0F746}, {0x2D5A6A36}, {0x3749919E}, {0x763470B3},
	{0xB58B5256}, {0x9A4335EA}, {0x0DDC6F12}, {0x26EA533C}, {0xC719DA31}, {0x4570AC6F}, {0x5770A1CB}, {0xAF284763},
	{0x5366AA1E}, {0x8C354FCC}, {0x1E9A339C}, {0x984E25FA}, {0x4E6926AD}, {0x671C4AD6}, {0x717D5C12}, {0xA443ECCE},
	{0x80D0BFE6}, {0x52AB5A66}, {0x0978ABBA}, {0x3656E346}, {0x9BBC409E}, {0x8F8067CB}, {0x2B7B43B0}, {0x1B8DE236},
	{0x88FF289A}, {0x56C3A572}, {0x86AF4666}, {0x88FA398E}, {0xA1507FB4}, {0x8D615A7C}, {0xD7724594}, {0xA71925AE},
	{0x4C52B5E9}, {0xE6163D34}, {0x8691AE7C}, {0x8378AB9A}, {0x07B3DA86}, {0x1D21FD62}, {0xB625543E}, {0x5D25A3B4},
	{0x9E095DF0}, {0x832D9E9C}, {0x65CA7C19}, {0x93378E86}, {0x904D9ABE}, {0x4389E2DE}, {0x195E8A8F}, {0x3B585999},
	{0x5C6F445C}, {0x760B7A45}, {0x5273D85A}, {0x947D89CC}, {0xD32B4674}, {0x928BE59C}, {0xC4D6730E}, {0x9453F70A},
	{0x7063B95C}, {0x7354E929}, {0xA4BA3B86}, {0x252AE72D}, {0x949B549E}, {0x468A5E75}, {0xDF0A4596}, {0x924BF4D4},
	{0x27DB5582}, {0x0F71AF50}, {0x5D4C7706}, {0x8377BC14}, {0xC6D8446F}, {0xE05D68BA}, {0x837EC456}, {0x2C4665F9},
	{0x97368F14}, {0x9A7E12C3}, {0x0C78CACF}, {0x8D192EBC}, {0x905CE71E}, {0x5FA3119C}, {0xD0F549A6}, {0x2AD92B2E},
	{0x5B20764F}, {0x37D321AA}, {0xC37324AE}, {0x991DEE05}, {0x8B996378}, {0xA3934DB8}, {0x57D03F14}, {0xB371523C},
	{0x79642F16}, {0xA7C70A1E}, {0xB83D216E}, {0x19F247C3}, {0xC405FB66}, {0x42EB7516}, {0x92ADBA26}, {0xC1F158AD},
	{0x20EA7D4E}, {0x15DCC44F}, {0x3D752B0C}, {0x1FD06D45}, {0xD83C3A27}, {0x2350EA6F}, {0x3D10D9B6}, {0x472DAB38},
	{0xA13B49DA}, {0x2F3D710C}, {0xA1BC3876}, {0x717E3192}, {0xC43E8AB5}, {0x992972AD}, {0x8E254EB9}, {0x7435D1D2},
	{0x757A2847}, {0x9564D82F}, {0x1D4DA91E}, {0x86FE8661}, {0x06B1BFC2}, {0x192CCBDA}, {0x0D4FE92A}, {0xA6831BF4},
	{0x54C17D1E}, {0x2FA21E59}, {0x39605BAE}, {0xE71C7225}, {0x0BDA649E}, {0x1B3CCD85}, {0x1B8D4CBA}, {0x665C1DA6},
	{0xA32A1E9E}, {0x8E854B7A}, {0x9C1AD2AD}, {0x92F03B63}, {0x7E1270E5}, {0x8767A52A}, {0x1CB5CD26}, {0x868B1FD8},
	{0x309ABE65}, {0x320DFA66}, {0x4D1DE296}, {0xDF24491E}, {0x87A5C9B8}, {0x0DE1A4BE}, {0xE7690671}, {0x30F01EAF},
	{0xD321C75A}, {0xF70B5D02}, {0xD3C25336}, {0x55E42E1E}, {0x34E3562D}, {0x96E5634C}, {0x51E958AD}, {0x84A67B36},
	{0xC2D6750E}, {0x3DA74394}, {0x516DE632}, {0x8E8E0CF5}, {0x8361CD7C}, {0x0A69BBA9}, {0xC13A5BA6}, {0x73575984},
	{0xC0D82EF3}, {0xB3199D64}, {0xB034BAC7}, {0x9292CD6E}, {0x6F186356}, {0x18E1D4F6}, {0xA44DB99A}, {0x1AA23BCE},
	{0xB6097A66}, {0xBA5D053C}, {0x09DEC5C9}, {0x58CD721E}, {0x8AD062FD}, {0x986F5D90}, {0xAD663156}, {0x732A522F},
	{0xE75909E4}, {0xC7D11C56}, {0x9E17705A}, {0x8E06D1FA}, {0x9A4336E6}, {0xF34816D9}, {0xD3C43556}, {0x968977C4},
	{0x85D2679C}, {0x2D666359}, {0x4F1569CA}, {0xA2529DCE}, {0xD27196C3}, {0x907AD752}, {0x62754CDA}, {0xA4BF412E},
	{0x706136ED}, {0xD3A83396}, {0x22EDB13C}, {0x77812EA9}, {0xA1BC703E}, {0x2E4B707A}, {0x985937F0}, {0x95C17E86},
	{0x39C94B5C}, {0x5B7CD203}, {0x9F6182B6}, {0x53B81A9E}, {0x068DFC5C}, {0xD3124FB4}, {0x5745D94A}, {0x4543FDD0},
	{0x8E47BD82}, {0x5A276A3C}, {0x5189BBA6}, {0xAF4A3619}, {0x83C5CD72}, {0x5743DD0C}, {0x0C7E9B23}, {0x13D9BC52},
	{0xC72D2AC6}, {0x8B2DC36C}, {0xB2B91E49}, {0x84DF1D8C}, {0x0B5BA8DC}, {0x354DA69C}, {0x51C7AC96}, {0x8A2ADF86},
	{0x750471F9}, {0xC766254E}, {0x9D730A3A}, {0x4427E5E9}, {0x70618DFC}, {0x63AC3E91}, {0x991D6E34}, {0x4BC34DB4},
	{0x48E16E3E}, {0x1AEA0F3A}, {0x84F5CCB4}, {0xD4292BB6}, {0x42E27CB3}, {0x451CFD43}, {0x18C64EDD}, {0x3AC54F1C},
	{0x44D2EF16}, {0x84CFE4A6}, {0x0A3ADF43}, {0xD24F28DA}, {0xC07459BE}, {0x824AEBBC}, {0x84C76F4C}, {0x42DD72C6},
	{0x29DA0ED9}, {0xCA1B5D52}, {0x0F41DAF4}, {0x9D6034F3}, {0xBF076425}, {0x822BB1EE}, {0x3E62705D}, {0xA1714FF0},
	{0x8672E5B2}, {0x7703C1DA}, {0x3176E40F}, {0xB7A506D1}, {0x44B46DF2}, {0x8F917A51}, {0x78656636}, {0x3438D3F4},
	{0x80DD7F42}, {0xD276A561}, {0x866FB90C}, {0x45DA6B85}, {0xD3B951C2}, {0x1E8E4F26}, {0x617C670B}, {0x56D86723},
	{0x2E7EB403}, {0x0EFE8E11}, {0xD46D9926}, {0x4A996B4E}, {0x0C78C5FC}, {0x1DB2719C}, {0xB9547951}, {0x9F213572},
	{0x3EE6031E}, {0x755D5B02}, {0x991BD196}, {0x8E46BE19}, {0x6C036DF4}, {0xAA2D6A4E}, {0x0D629EB3}, {0x07A896F3},
	{0x4A7C35C6}, {0x886AD73C}, {0x736E231A}, {0x4DB841F6}, {0xE35D49C2}, {0x19D072E7}, {0xB5B515D0}, {0x455DE0BA},
	{0xDE0C561B}, {0xB256C54E}, {0x96DF7102}, {0x9C05D4EE}, {0xA74445FA}, {0x742B5A74}, {0x06F588FA}, {0x84AD997A},
	{0x06C6BE55}, {0x53D2750D}, {0x1A5DF072}, {0x42DBCB54}, {0x2F0E18F3}, {0x44A9D3F4}, {0x4E41D97A}, {0x97803F5C},
	{0x574FC614}, {0x92BD8366}, {0x88C63FD2}, {0xB58B29B4}, {0x43F62A69}, {0x917B85CC}, {0x0DB3E1A6}, {0x496BC794},
	{0x91759B86}, {0x48F93E89}, {0x0A9678CF}, {0x2F374D90}, {0x3702F635}, {0x97C52AB2}, {0x471DE49A}, {0xA7E64531},
	{0xC119CDEC}, {0x96D93C1C}, {0x929A5D3A}, {0x244DF978}, {0xA3EB09B8}, {0xE2127B4E}, {0xA13DE9B0}, {0x469D6F42},
	{0xA73D185C}, {0x9BF21945}, {0x87CF05B4}, {0xC46967CC}, {0x0F30E6B6}, {0x2E7D04AE}, {0x8DB127B8}, {0xB74314E6},
	{0x7109EB74}, {0xA427B966}, {0x54C1DA3E}, {0xB34C1E95}, {0x4C6D723C}, {0x3B9E0A65}, {0x1934BAB3}, {0x495E4B99},
	{0x3457E962}, {0x94F1DC1A}, {0xA70B6AB2}, {0x317FA1C4}, {0x5E1073DA}, {0x82AFB546}, {0x8683EB9A}, {0xF043657A},
	{0x0DECB299}, {0x2774F154}, {0xA17349F4}, {0x96FB03A4}, {0x57D5640E}, {0x829CCABB}, {0xA1AD43B6}, {0x291CDAAD},
	{0x1859BE8E}, {0x86F4B90E}, {0x2ACB1D9C}, {0x9CD54752}, {0x185AF44F}, {0x2B276BC4}, {0xA17361DC}, {0xC3698BE4},
	{0xB56BB504}, {0xD9615176}, {0x53DE1951}, {0xD40CB2AF}, {0x94C78EA9}, {0x178BBE06}, {0x919DB970}, {0x4F674A85},
	{0x1A3DCF44}, {0x1BC5BD12}, {0x90ACED72}, {0x889E6F16}, {0xAE165D1C}, {0x16D0AE8F}, {0x1E907C5E}, {0x43986E9E},
	{0xB5681DB4}, {0xCF19149E}, {0x73734D22}, {0x706D43B6}, {0xD5293B94}, {0x354D9AC6}, {0x532EAA56}, {0x1D9AA9C9},
	{0xB3DA510D}, {0x1F589627}, {0x855CB95A}, {0x9129AF36}, {0x8FCA522D}, {0x8B21B2EE}, {0x987FD094}, {0x9DE5206D},
	{0xE6103B6E}, {0x3674A0AF}, {0xC8212FFC}, {0x6D70613E}, {0xC64A5CD6}, {0x91A93B6C}, {0x226FAA66}, {0xB319D52C},
	{0x23EF630C}, {0x8DC76616}, {0x95B342AE}, {0x50C57DCC}, {0x33ED1B44}, {0x1B4BF164}, {0x5E451EA6}, {0xD68F41C6},
	{0x3E464CD3}, {0x229AE1BE}, {0x927BF122}, {0x1D77E026}, {0xB5AC2396}, {0x38E54D3C}, {0xD4292EBC}, {0xC72B236C},
	{0x1DA9A35A}, {0xAA6D41E6}, {0x9721D56A}, {0xCF495629}, {0x0A74CBDA}, {0xC322EB65}, {0x447DD4C6}, {0x96498BF8},
	{0x9D47893C}, {0x9A19A57A}, {0x2E4BD456}, {0x3FBE0843}, {0x1586EB8E}, {0xB5091FCC}, {0x0AA5FC1E}, {0x8C423EF6},
	{0x4F1C6273}, {0x4C584EF6}, {0x1844DEF3}, {0x3DCD241E}, {0xC1E649F1}, {0x2C6B8EA9}, {0xB58B6296}, {0x707A39C5},
	{0x6B1A69E1}, {0x8D1B63A6}, {0x1DA57561}, {0x70CB7A29}, {0x96E32E34}, {0x0A9CB5E9}, {0x0BFB20F4}, {0x5C47A696},
	{0x13ADBC26}, {0xA2536E3C}, {0xDF0D41B2}, {0x07B9B94A}, {0x4C4F7398}, {0x95338BD4}, {0xC12FE998}, {0x15AE85D9},
	{0x85ED915A}, {0x936FA486}, {0xC65F0696}, {0x0CA3D9DA}, {0x9D3B1586}, {0xAB372916}, {0x50E760FC}, {0x1D21ABF8},
	{0x5A3C7076}, {0xF4497632}, {0x72D274A5}, {0x2C732EB4}, {0xB319FD04}, {0xA652BE25}, {0x53CF7510}, {0x1C97E1C6},
	{0x93C9DD42}, {0x3CAC34CB}, {0x3D31AD46}, {0x996F0B89}, {0x3655BC1A}, {0x8E47ACC6}, {0xB041D6DE}, {0xAD5B6161},
	{0x1979B0F4}, {0x84CD6F8A}, {0x4733A9AC}, {0x83D9F431}, {0x77C3059A}, {0x95CE0F52}, {0x3B2F0CD2}, {0xAE790E1C},
	{0x9BF602A5}, {0x496D4BCC}, {0xB2A71B34}, {0x2F1A296D}, {0xC50B9A9E}, {0xAB196BD0}, {0x1E954AAE}, {0x87932D9A},
	{0x9EA134F2}, {0x11CC9FC3}, {0x714438FB}, {0xD713B216}, {0xA350B93E}, {0x6A3A4B56}, {0x3E4A7075}, {0x85B9E5D0},
	{0x9E4338B6}, {0x387F50B4}, {0x42C56FCC}, {0x57917694}, {0x1586DEE1}, {0x741B29EA}, {0xA32B0EF2}, {0x8B599C8B},
	{0xCC5E7129}, {0x961BFB02}, {0x27F9821E}, {0x96FD5302}, {0x41EE83E9}, {0x55A5D469}, {0x5B5D3419}, {0xA66AD172},
	{0x32EA473C}, {0x9ED05369}, {0x0ECD91BA}, {0x720A5F65}, {0x1CA73BA4}, {0x1DA534E3}, {0xAB79072C}, {0x4C5EB643},
	{0x8D5D9926}, {0xF0250FBA}, {0x1795DE11}, {0x0E299DF8}, {0xC74D2AA6}, {0x3F41578A}, {0xB06EE50E}, {0x51BC486F},
	{0x76230BB6}, {0x26F23792}, {0x716964B9}, {0x1DFA9485}, {0xAC2E6A1E}, {0x30EB3C66}, {0xF0305DE9}, {0x1877BD90},
	{0x917DB066}, {0x971AA0F3}, {0x17C69E49}, {0x3A776446}, {0x0BBC25E3}, {0x8F832F2A}, {0xD0099EBE}, {0x5D317A32},
	{0x096ADB9C}, {0x571C868F}, {0x926CAD5A}, {0xA4391CEE}, {0xD1E86656}, {0x73890DBA}, {0x70E67E11}, {0xC6612DEA},
	{0x8799654E}, {0xCE4C5786}, {0x9E4358D6}, {0xA74D4C9C}, {0xA549D25E}, {0x74E1473A}, {0xF27023F2}, {0x9D0D8CD9},
	{0x04ECD1FC}, {0xD41978BC}, {0x3D674C54}, {0x71A94D72}, {0x8D7E40C7}, {0x978E253A}, {0x78271AE9}, {0x74355C9C},
	{0xC343F31C}, {0x764609FC}, {0x25983BCB}, {0x742B8E36}, {0xD48B65CC}, {0x25EC1A3B}, {0xA5CE093E}, {0x9E6531CC},
	{0x12B1FC2E}, {0x428BAE9E}, {0x53F5620E}, {0x1F34D983}, {0x57CD0A3C}, {0x28697E72}, {0x93BC0F1A}, {0x384C4DFC},
	{0x4EDE7205}, {0x4E1D4CBC}, {0x3C2E895E}, {0x6609F752}, {0x5F181F92}, {0x90DF53B0}, {0x3D264CD6}, {0x86D6E075},
	{0x42DB65D8}, {0xD6D0616E}, {0x96D53570}, {0x94B0CBE6}, {0x83B2F4A5}, {0x5969B346}, {0x8C276E99}, {0x37B531C2},
	{0x6A477592}, {0x2A7A2C3E}, {0xB54EC259}, {0xB151A5E6}, {0x1385FF90}, {0x7141F83E}, {0x5A122FCB}, {0xA5F4059E}
};
