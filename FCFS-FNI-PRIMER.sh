#!/bin/bash

############################################################################################################
#              INICIO
############################################################################################################
#
# Script que permite simular la secuencia de entrada/salida en memoria de una serie de procesos. El
# algoritmo que se sigue para la entrada/salida en memoria es FCFS-SJF y se consideran particiones fijas
# no iguales.
#
# Además, la asignación se hace con ajuste primer (el primer sitio donde haya hueco es donde entra).
#
# Se permite interacción con el ususario para selección de procesos y particiones. Y se genera un informe
# con la secuencia de ejecuciones realizadas.
#
# ----------------------------------------------------------------------------------------------------------
#
# NUEVO ALUMNO:  Ignacio Zaldo González (2023)
#
# ANTERIORES ALUMNOS: Ismael Manzanera López, Rodrigo Merino Tovar, Omar Santos Bernabé, Marcos Pena Calvar, David Cacho Saiz, Miguel Ángel Vidal Sevillano, Maria Teresa Quintanal
#
# FECHA: Abril de 2023
#
# LICENCIA: Creative Commons
#
# VERSION 6: 2023 Se ha cambiado de ajuste mejor a primer
########################################################################################################################
########################################################################################################################
####################################                                       ###################################################################
####################################            COMPLETAR                  ###################################################################
####################################                                       ###################################################################
########################################################################################################################
########################################################################################################################
#
# VERSION 5: 2022 Se ha mejorado todo el código para que sea más legible, para ello, se ha modulado todo el código en diferentes ficheros.
#                 Se mejoran todos los comentarios del código.
#                 Se ha mejorado todos los nombres de las variables y funciones.
#                 Se ha añadido la funcionalidad de que el usuario pueda escoger el fichero que le convenga para cargarlo en el programa.
#
#
# VERSION 4: 2020 Se incluye el cambio por completo del algoritmo desde un FCFS, por SJF SRPT
#                 Se cargan todos los procesos para su tratamiento apropiativo como caracterisitca nueva.
#                 Se mantiene el mejor ajuste pero invadiendo a los procesos en ejecucion.
#
# VERSIÓN 3: 2018 Se incluye el 'tiempo restante' de los procesos durante la ejecución
#
#     Se modifica la línea temporal de ejecución de procesos para que aparezca el color del proceso
#     ejecutando durante el instante de tiempo y no antes.
#
#
#
# VERSIÓN 2: 2018 Se hace una línea temporal de ejecución de procesos más intuitiva. Mostrando únicamente
#     el nombre del proceso correspondiente y el instante de tiempo en el que comienza a ejectuar
#
#     La introducción de nombres de procesos ahora se hace forma automática. Se elimina así la
#     necesidad de comprobar nombres y ver si cumplen los requesitos necesarios.
#
#     Se introducen comandos que permiten generar un informe a color
#
#     Se muestran los procesos ordenados en una tabla, de forma más intutiva para el usuario
#
#     Se incluye un único documento para entrada de datos de particiones y procesos. Este
#     nuevo documento se llama 'FicheroEntradaDatosPredefinidos.txt'. Con esto se condige eliminar
#     el exceso de documentos por cada práctica, ya que este nuevo archivo sustituye a
#     'EntradaProcesosPredefinidos.txt' y 'EntradaParticionesPredefinidas.txt'
#
#
#
# VERSIÓN 1: 2018 Se separa todo el código en funciones. Con lo cual se mejora la escalabilidad. Gran parte del
#     trabajo realizado se ha centrado en esta mejora. Algo fundamental en la programación estructura
#     y que permitirá mejor adaptación del script en un futuro.
#
#     Se establecen menús para mejorar la interacción con el usuario
#
#     Hasta ahora, si todos los procesos llegaban después del instante 0, el script
#     no se ejecutaba de forma adecuada. Se repara estableciendo el tiempo de inicio de reloj
#     con el tiempo de llegada del primer proceso
#
#     Otro de los cambios importantes ha sido añadir 'huecos' del tipo [  ] en la representación
#     gráfica de los instantes en los que no hay procesos ejecutando
#
#
#     Se comenta gran parte del algoritmo principal de SRPT para mejor lectura del desarrollador
#
#     Se asigna color a las salidas por pantalla para mejor interacción con el usuario
#
#     Se muestra al usuario el estado de las particiones y los procesos seleccionafdos (tanto de
#     fichero como de teclado) después de ordenarlos. Con esto se mejora la interacción con
#     el usuario y se entiende mejor el proceso que se está siguiendo. Hasta ahora se ordenaban
#     pero no se mostraban
#
#     Se mejora la introducción de nombres de procesos (en caso de hacerlo por teclado)
#     controlando límite de caracteres
#
#     Se elimina multitud de código innecesario. Gran parte del código eliminado correspondía
#     con salidas a pantalla/informe que estaban duplicadas (se soluciona con 'tee')
#
#     Se incorpora la opción de mostrar un breve manual de usuario en formato .pdf
#
#     Se mejoran los nombres de varios arrays y variables para facilitar comprensión del
#     desarrollador
#
#     Se añaden fecha y hora de última ejecución en el informe final

############################################################################################################
#                                         VARIABLES
############################################################################################################

#OPCIONES DE INTRODUCCIÓN DE DATOS POR PARTE DEL USUARIO
tipoDeEjecucion=1           #Varible de opcion de usuario para introducion de datos 1-Nueva ejecucion 2-Ultima ejecucion
particionesTecladoFichero=1 #Variable de opcion para introduccion de particiones 1-Por teclado 2-Por fichero
masparticion=s              #Variable bandera que determina si el usuario desea introducir mas particiones. Inicializada a s (sí)
contadorParticiones=1       #Contador para la introduccion de particiones
masprocesos=s               #Variable bandera que determina si el usuario desea introducir mas particiones
numero=0

################################################################################################################################################################################################
#                                VARIABLES DEL ALGORITMO Y GESTIÓN DE DATOS
################################################################################################################################################################################################
p=1              # contador
i=1              # contador
j=0              # contador
k=0              # contador
contador=0       # contador
suma_espera=0    # variable donde se acumula la suma de los tiempos de espera de todos los procesos
suma_respuesta=0 # variable donde se acumula la suma de los tiempos de respuesta de todos los procesos
espera=0         # variable donde se acumula el tiempo de espera correspondiente a dicho proceso
respuesta=0      # variable donde se acumula el tiempo de respuesta correspondiente a dicho proceso
suma_ejecucion=0 # variable donde se acumula la suma de los tiempos de ejecucion
tinicio=0        # variable que se guarda el tiempo de inicio del proceso
aux=0            # variable auxiliar utilizada para intercambiar valores
palabra=0        # variable donde se almacena el nombre durante el proceso de validacion de entrada de datos
valido=0         # variable bandera en validacion
lineaspart=0     # variable que almacena el numero de lineas de fichero de entrada de particiones
a=0              # variable auxiliar utilizada para intercambiar valores
b=0              # variable auxiliar utilizada para intercambiar valores
nombre=0         # variable auxiliar para almacenar nombre de procesos
salida=n         # variable que indica que la ejecucion de todos los procesos ha finalizado
hasalido=0       # variable que indica que un proceso ha finalizado la ejecucion
reloj=0          # variable que guarda el tiempo de ejecucion
saliente=0       # variable que indica que un proceso acaba de finalizar la ejecucion
booleano=1       # variable bandera auxiliar
enterContinuar=0 #Variable para hacer una continuar alamacenando valor en variable sin uso posterior
DIA=0            #Variable para mostrar el día de la última ejecución en informe de salida
HORA=0           #Variable para mostrar la hora de la última ejecución en informe de salida
semaforo=0       #Variable semaforo para controlar acceso o parada de un proceso
expulsar=0       #Variable semaforo para controlar acceso o parada de un proceso en una expulsión (SRPT)
px=0
part=0
abortar=0
################################################################################################################################################################################################
#VARIABLES DE REPRESENTACIÓN DEL MAPA DE MEMORIA
################################################################################################################################################################################################
espaciomemoria=79         # numero de caracteres que ocupara la representacion de la particion mas grande
representacionparticion=0 # numero de caracteres que ocupara la representacion de la particion que se va a representar
representacionproceso=0   # numero de caracteres que ocupara la representacion del proceso que ocupa dicha particion
num_carac=0               # numero de caracteres que ocupa el nombre del proceso
espacionombre=18          # numero de caracteres que debe ocupar el nombre del proceso y el espacio de alineacion
espacios=0                # numero de caracteres que debe ocupar el espacio para alineacion
terminal=0
division=0
caracterestotales=4
numerodelineas=0
columnasporfila=0
columnasporfila2=0
numeroSeparadores=0
separadores=0
nseparadores=0
cuentacolumnas=0
caracteresPorLinea=$(($(tput cols) - 3))
representacionvacia="---------------" # representacion que se producira cuando no exista ningun proceso ocupando la particion
particionrepresentada=0               # numero de particion que se va a representar
variablepropia=0

esc=$(echo -en "\033")
################################################################################################################################################################################################
#VARIABLES PARA DESTACAR TEXTO CON COLOR
################################################################################################################################################################################################
ROJO=$esc"[1;31m"
VERDE=$esc"[1;32m"
CYAN=$esc"[1;36m"
AZUL=$esc"[1;34m"
AMARILLO=$esc"[1;33m"
MORADO=$esc"[1;35m"
NORMAL=$esc"[1;m"

################################################################################################################################################################################################
#VARIABLES PARA DESTACAR TEXTO CON COLOR FONDO
################################################################################################################################################################################################
ROJO2=$esc"[41m"
VERDE2=$esc"[42m"
CYAN2=$esc"[46m"
AZUL2=$esc"[44m"
AMARILLO2=$esc"[43m"
MORADO2=$esc"[45m"
NORMAL2=$esc"[1;m"

#VECTORES
proceso=()                #Almacena el nombre de cada proceso indicado por el usuario
llegada=()                # tiempo de llegada de los procesos
tiempo=()                 # tiempo de ejecucion de los procesos
memoria=()                # espacio en memoria requerido por el proceso
tiempoEsperaProceso=()    # tiempo de espera de los procesos
tiempNEsperaProceso=()    # tiempo de espera de los procesos (0 si es negativo)
tiempoRespuestaProceso=() # tiempo de respuesta de los procesos
tiempoNRespuProceso=()    # tiempo de respuesta de los procesos (0 si es negativo)
partConProceso=()         # particion ocupada por un proceso
particiones=()            # vector donde se almacenan las particiones
colores=()                # vector donde se almacenan los colores
colores2=()               # vector donde se almacenan los colores para el fondo del texto
coloresfondo=()           # vector donde se almacenan los colores de fondo
procesoejecutado=()       # vector donde se almacenan los procesos ejecutados en cada uno de los instantes
bloqueo=()                # vector que almacena (0/1) para bloquear un reset de tiemp ejec inicial
sale=()                   # vector que indica si un Px ha salido o no

################################################################################################################################################################################################
#VECTORES TEMPORALES PARA ALMACENAR ANTES DE COMPROBACIÓN PREVIA
################################################################################################################################################################################################
proceso2=() # nombre del proceso
llegada2=() # tiempo de llegada
tiempo2=()  # tiempo de ejecucion
memoria2=() # espacio en memoria
profich=()  # vector auxiliar para entrada de procesos por fichero
proficheroentrada=()

################################################################################################################################################################################################
#VECTORES DE COLORES
################################################################################################################################################################################################
colores[0]=$ROJO
colores[1]=$VERDE
colores[2]=$CYAN
colores[3]=$AZUL
colores[4]=$AMARILLO
colores[5]=$MORADO

################################################################################################################################################################################################
#VECTORES DE COLORES2
################################################################################################################################################################################################
colores2[0]=$ROJO2
colores2[1]=$VERDE2
colores2[2]=$CYAN2
colores2[3]=$AZUL2
colores2[4]=$AMARILLO2
colores2[5]=$MORADO2

################################################################################################################################################################################################
# Ficheros de salida.
################################################################################################################################################################################################
informeSinColor="./FLast/informeBN.txt"
informeConColor="./FLast/informeCOLOR.txt"
ficheroanteriorejecucion="./FLast/DatosLast.txt"
ficherodatosaleatorios="./FRangos/DatosRangosLast.txt"
ficherodatosaleatorios_totales="./FRangosAleT/FRangosAleTotal.txt"
ficherosubrangos_totales="./FRangos/DatosRangosDefault.txt"
ficherorangos_totales="./FRangosAleT/DatosRangosAleTotalDefault.txt"
ficherodatosdefault="./FDatos/DatosDefault.txt"
cp ./FLast/DatosLast.txt ./FDatos/DatosDefault.txt
cp ./FRangos/DatosRangosDefault.txt ./FLast/RangosSubrangos.txt
cp ./FRangosAleT/DatosRangosAleTotalDefault.txt ./FLast/RangosAleTotalLast.txt
cp ./FRangos/DatosRangosDefault.txt ./FLast/DatosRangosLast.txt
################################################################################################################################################################################################
################################################################################################################################################################################################
#             FUNCIONES
################################################################################################################################################################################################
################################################################################################################################################################################################
# Sinopsis:   Menú de elección de opciones del programa
################################################################################################################################################################################################

function menueleccion {

    clear

    echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL
    echo -e "\n1. Introducción de datos manual"
    echo -e "\n2. Fichero de datos de última ejecución (DatosLast.txt)"
    echo -e "\n3. Otros ficheros de datos"
    echo -e "\n4. Aleatorio manual (Indica rango)"
    echo -e "\n5. Fichero de rangos de última ejecución (DatosRangosLast.txt)"
    echo -e "\n6. Otros ficheros de rangos"
    echo -e "\n7. Rangos aleatorios totales"
    echo -e "\n8. Salir"
    echo -n -e "\n--> "
    read seleccion

    echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL >>$informeConColor
    echo -e "\n1. Introducción de datos manual" >>$informeConColor
    echo -e "\n2. Fichero de datos de última ejecución (DatosLast.txt)" >>$informeConColor
    echo -e "\n3. Otros ficheros de datos" >>$informeConColor
    echo -e "\n4. Aleatorio manual (Indica rango)" >>$informeConColor
    echo -e "\n5. Fichero de rangos de última ejecución (DatosRangosLast.txt)" >>$informeConColor
    echo -e "\n6. Otros ficheros de rangos" >>$informeConColor
    echo -e "\n7. Rangos aleatorios totales" >>$informeConColor
    echo -e "\n8. Salir" >>$informeConColor
    echo -n -e "\n--> $seleccion" >>$informeConColor

    echo -e "\nMENÚ INICIO" >>$informeSinColor
    echo -e "\n1. Introducción de datos manual" >>$informeSinColor
    echo -e "\n2. Fichero de datos de última ejecución (DatosLast.txt)" >>$informeSinColor
    echo -e "\n3. Otros ficheros de datos" >>$informeSinColor
    echo -e "\n4. Aleatorio manual (Indica rango)" >>$informeSinColor
    echo -e "\n5. Fichero de rangos de última ejecución (DatosRangosLast.txt)" >>$informeSinColor
    echo -e "\n6. Otros ficheros de rangos" >>$informeSinColor
    echo -e "\n7. Rangos aleatorios totales" >>$informeSinColor
    echo -e "\n8. Salir" >>$informeSinColor
    echo -n -e "\n--> $seleccion" >>$informeSinColor

    ################################################################################################################################################################################################
    #Comprobación de que el número introducido por el usuario esta entre el 1 y el 8
    ################################################################################################################################################################################################
    while [[ 1 -lt $seleccion || $seleccion -lt 8 ]]; do
        case "$seleccion" in
        '1')
            nuevaEjecucion
            entradaParticionesTeclado
            entradaProcesosTeclado
            tiempoejecucionalgormitmo
            break
            ;;

        '2')
            tiempoejecucionalgormitmo
            anteriorEjecucion

            break
            ;;

        '3')
            entradaParticionesFichero
            entradaProcesosFichero
            tiempoejecucionalgormitmo
            break
            ;;

        '4')
            entradaProcesosRangoManual_op_cuatro
            tiempoejecucionalgormitmo
            break
            ;;

        '5')
            entradaParticionesRangoFichero_predefinido
            entradaProcesosRangoManual_op_cinco
            tiempoejecucionalgormitmo
            break
            ;;

        '6')
            entradaParticionesRangoFichero
            entradaProcesosRangoManual_pruebas
            tiempoejecucionalgormitmo
            break
            ;;

        '7')
            entradaParticionesRangoFichero_PRED
            entradaProcesosRangoManual_op_siete
            tiempoejecucionalgormitmo
            break
            ;;

        '8')
            echo -e $ROJO"\nSE HA SALIDO DEL PROGRAMA"$NORMAL
            exit 0
            break
            ;;

        *)
            clear
            echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL
            echo -e "\n1. Introducción de datos manual"
            echo -e "\n2. Fichero de datos de última ejecución (DatosLast.txt)"
            echo -e "\n3. Otros ficheros de datos"
            echo -e "\n4. Aleatorio manual (Indica rango)"
            echo -e "\n5. Fichero de rangos de última ejecución (DatosRangosLast.txt)"
            echo -e "\n6. Otros ficheros de rangos"
            echo -e "\n7. Salir"
            echo -n -e "\n--> "
            read seleccion
            ;;
        esac
    done
}

################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################

################################################################################################################################################################################################
#  Sinopsis:   menú de elección de algoritmo a usar (FCFS o SJF)
################################################################################################################################################################################################

function menuAlgoritmo {
    clear
    echo -e $AMARILLO"\nMENÚ DE ELECCIÓN DE ALGORITMO"$NORMAL
    echo -e "\n1. FCFS"
    echo -e "\n2. SJF"
    echo -e "\n3. SRPT"
    echo -e "\n4. Salir"
    echo -n -e "\n--> "
    read algoritmoE

    echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL >>$informeConColor
    echo -e "\n1. FCFS" >>$informeConColor
    echo -e "\n2. SJF" >>$informeConColor
    echo -e "\n3. SRPT" >>$informeConColor
    echo -e "\n4. Salir" >>$informeConColor
    echo -n -e "\n--> " >>$informeConColor
    echo "$algoritmoE" >>$informeConColor
    echo "" >>$informeConColor

    echo -e "\nMENÚ INICIO" >>$informeSinColor
    echo -e "\n1. FCFS" >>$informeSinColor
    echo -e "\n2. SJF" >>$informeSinColor
    echo -e "\n3. SRPT" >>$informeSinColor
    echo -e "\n4. Salir" >>$informeSinColor
    echo -n -e "\n--> " >>$informeSinColor
    echo "$algoritmoE" >>$informeSinColor
    echo "" >>$informeSinColor

    ################################################################################################################################################################################################
    #Comprobación de que el número introducido por el usuario es 1, 2 ó 3
    ################################################################################################################################################################################################

    while [[ 1 -lt $algoritmoE || $algoritmoE -lt 3 ]]; do
        case "$algoritmoE" in
        '1')

            menueleccion
            break
            ;;

        '2')

            menueleccion
            break
            ;;

        '3')

            continuarProgramaPrincipal
            break
            ;;

        '4')
            echo -e $ROJO"\nSE HA SALIDO DEL PROGRAMA"$NORMAL
            exit 0
            break
            ;;

        *)
            clear
            echo -e $AMARILLO"\nMENÚ DE ELECCIÓN DE ALGORITMO"$NORMAL
            echo -e "\n1. FCFS"
            echo -e "\n2. SJF"
            echo -e "\n3. SRPT"
            echo -e "\n4. Salir"
            echo -n -e "\n--> "
            read algoritmoE

            echo -e $AMARILLO"\nMENÚ DE ELECCIÓN DE ALGORITMO"$NORMAL >>$informeConColor
            echo -e "\n1. FCFS" >>$informeConColor
            echo -e "\n2. SJF" >>$informeConColor
            echo -e "\n3. SRPT" >>$informeConColor
            echo -e "\n4. Salir" >>$informeConColor
            echo -n -e "\n--> " >>$informeConColor
            echo "$algoritmoE" >>$informeConColor
            echo "" >>$informeConColor

            echo -e "\nMENÚ DE ELECCIÓN DE ALGORITMO" >>$informeSinColor
            echo -e "\n1. FCFS" >>$informeSinColor
            echo -e "\n2. SJF" >>$informeSinColor
            echo -e "\n3. SRPT" >>$informeSinColor
            echo -e "\n4. Salir" >>$informeSinColor
            echo -n -e "\n--> " >>$informeSinColor
            echo "$algoritmoE" >>$informeSinColor
            echo "" >>$informeSinColor
            ;;
        esac
    done
}

################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################

################################################################################################################################################################################################
# Sinopsis:   cabecera para mostrar por pantalla al inicio del programa y enviar a informe
################################################################################################################################################################################################
function presentacionPantallaInforme {

    echo "$AMARILLO"
    echo "########################################################################" | tee $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "#                           CREATIVE COMMONS                           #" | tee -a $informeSinColor
    echo "#                          ------------------                          #" | tee -a $informeSinColor
    echo "# - BY: reconocimiento (BY)                                            #" | tee -a $informeSinColor
    echo "# - NC: uso no comercial (NC)                                          #" | tee -a $informeSinColor
    echo "# - SA: compartir igual (SA)                                           #" | tee -a $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "########################################################################" | tee -a $informeSinColor
    echo "" | tee -a $informeSinColor
    echo "########################################################################" | tee -a $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "#          ALGORITMO FCFS CON PARTICIONES FIJAS NO IGUALES             #" | tee -a $informeSinColor
    echo "#                          Y AJUSTE PRIMER                             #" | tee -a $informeSinColor
    echo "#        --------------------------------------------------            #" | tee -a $informeSinColor
    echo "# - NUEVO ALUMNO:       Ignacio Zaldo González                         #" | tee -a $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "# - ALUMNO ANTERIOR:    Ismael Manzanera López                         #" | tee -a $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "# - ASIGNATURA:         Sistemas Operativos                            #" | tee -a $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "# - GRADO:              Ingeniería informática - 2023                  #" | tee -a $informeSinColor
    echo "#                                                                      #" | tee -a $informeSinColor
    echo "########################################################################" | tee -a $informeSinColor
    echo "$NORMAL"
    echo "" >>$informeSinColor
    DIA=$(date +"%d/%m/%Y")
    HORA=$(date +"%H:%M")
    echo -en "\nÚLTIMA EJECUCIÓN: " >>$informeSinColor
    echo "$DIA - $HORA" >>$informeSinColor
    echo "" >>$informeSinColor

    ################################################################################################################################################################################################
    #Salida para informe a color:
    ################################################################################################################################################################################################

    echo -e "\e[1;33m########################################################################" >$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m#                           CREATIVE COMMONS                           #" >>$informeConColor
    echo -e "\e[1;33m#                          ------------------                          #" >>$informeConColor
    echo -e "\e[1;33m# - BY: reconocimiento (BY)                                            #" >>$informeConColor
    echo -e "\e[1;33m# - NC: uso no comercial (NC)                                          #" >>$informeConColor
    echo -e "\e[1;33m# - SA: compartir igual (SA)                                           #" >>$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m########################################################################" >>$informeConColor
    echo "" >>$informeConColor
    echo -e "\e[1;33m########################################################################" >>$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m#          ALGORITMO FCFS CON PARTICIONES FIJAS NO IGUALES             #" >>$informeConColor
    echo -e "\e[1;33m#                          Y AJUSTE PRIMER                             #" >>$informeConColor
    echo -e "\e[1;33m#        --------------------------------------------------            #" >>$informeConColor
    echo -e "\e[1;33m# - NUEVO ALUMNO:       Ignacio Zaldo González                         #" >>$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m# - ALUMNO ANTERIOR:    Ismael Manzanera López                         #" >>$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m# - ASIGNATURA:         Sistemas Operativos                            #" >>$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m# - GRADO:              Ingeniería informática - 2023                  #" >>$informeConColor
    echo -e "\e[1;33m#                                                                      #" >>$informeConColor
    echo -e "\e[1;33m########################################################################" >>$informeConColor

    echo "" >>$informeConColor
    DIA=$(date +"%d/%m/%Y")
    HORA=$(date +"%H:%M")
    echo -en $NORMAL"ÚLTIMA EJECUCIÓN: " >>$informeConColor
    echo "$DIA - $HORA" >>$informeConColor
    echo "" >>$informeConColor

    echo -ne $ROJO"\nPulsa ENTER para comenzar "$NORMAL
    read enterContinuar
}

################################################################################################################################################################################################
# Sinopsis:   breve menú inicial con opción de mostrar manual de usuario
################################################################################################################################################################################################

function menuInicio {
    clear
    echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL
    echo -e "\n1. Ver manual de usuario (requiere 'evince')"
    echo -e "\n2. Acceder al programa principal"
    echo -e "\n3. Salir"
    echo -n -e "\n--> "
    read numero

    echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL >>$informeConColor
    echo -e "\n1. Ver manual de usuario (requiere 'evince')" >>$informeConColor
    echo -e "\n2. Acceder al programa principal" >>$informeConColor
    echo -e "\n3. Salir" >>$informeConColor
    echo -n -e "\n--> " >>$informeConColor
    echo "$numero" >>$informeConColor
    echo "" >>$informeConColor

    echo -e "\nMENÚ INICIO" >>$informeSinColor
    echo -e "\n1. Ver manual de usuario (requiere 'evince')" >>$informeSinColor
    echo -e "\n2. Acceder al programa principal" >>$informeSinColor
    echo -e "\n3. Salir" >>$informeSinColor
    echo -n -e "\n--> " >>$informeSinColor
    echo "$numero" >>$informeSinColor
    echo "" >>$informeSinColor

    ################################################################################################################################################################################################
    #Comprobación de que el número introducido por el usuario es 1, 2 ó 3
    ################################################################################################################################################################################################

    while [[ 1 -lt $numero || $numero -lt 3 ]]; do
        case "$numero" in
        '1')
            manualDeUsuario
            break
            ;;

        '2')
            menuAlgoritmo # aqui pongo el menú nuevo, que me permite elegir entre FCFS o SJF
            break
            ;;

        '3')
            echo -e $ROJO"\nSE HA SALIDO DEL PROGRAMA"$NORMAL
            exit 0
            break
            ;;

        *)
            clear
            echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL
            echo -e "\n1. Ver manual de usuario (requiere 'evince')"
            echo -e "\n2. Acceder al programa principal"
            echo -e "\n3. Salir"
            echo -n -e "\n--> "
            read numero

            echo -e $AMARILLO"\nMENÚ INICIO"$NORMAL >>$informeConColor
            echo -e "\n1. Ver manual de usuario (requiere 'evince')" >>$informeConColor
            echo -e "\n2. Acceder al programa principal" >>$informeConColor
            echo -e "\n3. Salir" >>$informeConColor
            echo -n -e "\n--> " >>$informeConColor
            echo "$numero" >>$informeConColor
            echo "" >>$informeConColor

            echo -e "\nMENÚ INICIO" >>$informeSinColor
            echo -e "\n1. Ver manual de usuario (requiere 'evince')" >>$informeSinColor
            echo -e "\n2. Acceder al programa principal" >>$informeSinColor
            echo -e "\n3. Salir" >>$informeSinColor
            echo -n -e "\n--> " >>$informeSinColor
            echo "$numero" >>$informeSinColor
            echo "" >>$informeSinColor
            ;;
        esac
    done
}

################################################################################################################################################################################################
# Sinopsis:   breve explicación sobre cómo funciona el script y lo que podemos hacer con él
################################################################################################################################################################################################

function manualDeUsuario {
    clear
    evince ./ManualDeUsuario.pdf
    menuInicio
}

################################################################################################################################################################################################
# Sinopsis:   cuando el usuario no necesita consultar el manual, porque conoce el funcionamiento,
#       se le permite continuar usando esta función (opción 2 del menú)
################################################################################################################################################################################################

function continuarProgramaPrincipal {
    clear
    menueleccion

}

################################################################################################################################################################################################
# Sinopsis:   elimina los archivos que había anteriormente creados y nos direcciona a la entrada de
#       particiones y procesos
################################################################################################################################################################################################

function nuevaEjecucion {
    clear
    rm $ficheroanteriorejecucion
}

################################################################################################################################################################################################
# Sinopsis:   permite utilizar los datos de particiones y procesos que se usaron en la última ejecución
################################################################################################################################################################################################

function anteriorEjecucion {
    ##############################################################################################
    #Salida del resultado de la entrada de las particiones
    ##############################################################################################
    lineaspart=($(cat $ficheroanteriorejecucion | grep "Particion" | cut -f 1 -d " " | wc -l))
    for ((i = 0; i < $lineaspart; i++)); do
        a=($(cat $ficheroanteriorejecucion | grep "Particion" | cut -f 2 -d " "))
        contadorParticiones=a[$i]
        nparti=($(cat $ficheroanteriorejecucion | grep "Particion" | cut -f 3 -d " "))
        particiones[$contadorParticiones]=${nparti[$i]}
    done

    llegada2=($(cat $ficheroanteriorejecucion | grep "Llegada" | cut -f 2 -d" "))
    tiempo2=($(cat $ficheroanteriorejecucion | grep "Llegada" | cut -f 4 -d" "))
    memoria2=($(cat $ficheroanteriorejecucion | grep "Llegada" | cut -f 6 -d" "))
    profich=($(cat $ficheroanteriorejecucion | grep "Llegada" | cut -f 1 -d " " | wc -l))

    ##############################################################################################
    ##############################################################################################
    #Ordenacion de procesos por llegada
    ##############################################################################################
    ##############################################################################################
    for ((j = $profich; j > 0; j--)); do
        for ((i = 0; i < j; i++)); do
            if [[ ${llegada2[$i]} -gt ${llegada2[$(($i + 1))]} && $i -lt $(expr $profich-1) ]]; then
                aux=${llegada2[$(($i + 1))]}
                llegada2[$(($i + 1))]=${llegada2[$i]}
                llegada2[$i]=$aux

                aux=${tiempo2[$(($i + 1))]}
                tiempo2[$(($i + 1))]=${tiempo2[$i]} #para ordenar los tiempos de ejecucion con sus tiempos de respuesta
                tiempo2[$i]=$aux

                aux=${proceso2[$(($i + 1))]}
                proceso2[$(($i + 1))]=${proceso2[$i]} #para ordenar los nombres con sus mismos valores
                proceso2[$i]=$aux

                aux=${memoria2[$(($i + 1))]}
                memoria2[$(($i + 1))]=${memoria2[$i]} #para ordenar la memoria con sus mismos valores
                memoria2[$i]=$aux

            fi
        done
    done

    for ((p = 1; p <= $profich; p++)); do
        if [ $p -gt 9 ]; then
            proceso[$p]=$(echo P$(($p)))
        else
            proceso[$p]=$(echo P0$(($p)))
        fi
        llegada[$p]=${llegada2[$(($p - 1))]}
        tiempo[$p]=${tiempo2[$(($p - 1))]}
        memoria[$p]=${memoria2[$(($p - 1))]}
    done

}

################################################################################################################################################################################################
# Sinopsis:   función que permite introducir particiones por teclado
################################################################################################################################################################################################

function entradaParticionesTeclado {
    while [[ "$masparticion" = "s" ]]; do
        echo -ne "\nIntroduce el tamaño de la partición $contadorParticiones:  "
        echo -ne "\nIntroduce el tamaño de la partición $contadorParticiones:  " >>$informeConColor
        echo -ne "\nIntroduce el tamaño de la partición $contadorParticiones:  " >>$informeSinColor
        read particiones[$contadorParticiones]
        echo "${particiones[$contadorParticiones]}" >>$informeConColor
        echo "${particiones[$contadorParticiones]}" >>$informeSinColor
        echo "Particion $contadorParticiones ${particiones[$contadorParticiones]}" >>$ficheroanteriorejecucion
        echo -ne "\n¿Quieres introducir otra partición? s/n  "
        echo -ne "\n¿Quieres introducir otra partición? s/n  " >>$informeConColor
        echo -ne "\n¿Quieres introducir otra partición? s/n  " >>$informeSinColor
        read masparticion
        echo "$masparticion" >>$informeConColor
        echo "$masparticion" >>$informeSinColor
        echo "" >>$informeSinColor
        echo "" >>$informeConColor

        until [[ $masparticion = "s" || $masparticion = "n" ]]; do
            echo -ne "\nEscribe 's' o 'n', por favor: "
            echo -ne "\nEscribe 's' o 'n', por favor: " >>$informeConColor
            echo -ne "\nEscribe 's' o 'n', por favor: " >>$informeSinColor
            read masparticion
            echo "$masparticion" >>$informeConColor
            echo "$masparticion" >>$informeSinColor
            echo "" >>$informeSinColor
            echo "" >>$informeConColor
        done
        let contadorParticiones=$contadorParticiones+1
    done
}

################################################################################################################################################################################################
# Sinopsis:   función que se encarga de realizar las preguntar para guardarlas.
################################################################################################################################################################################################

function Guardado {
    opcion=1 #opcion por defecto
    while [ $opcion -ne 2 ]; do
        echo -ne $AMARILLO"\n\n¿Dónde quieres guardar los rangos?"$NORMAL
        echo -ne $AMARILLO"\n1. En el fichero de rangos de última ejecución ($ficherodatosaleatorios)."$NORMAL
        echo -ne $AMARILLO"\n2. En otros ficheros de rangos."$NORMAL
        echo -ne $AMARILLO"\n\nIntroduce una opción: "$NORMAL
        read option2

        case $option2 in
        1)
            #Guardamos los rango s en datosrangos.txt
            echo "Particion minima $cantidad_rango_minima maxima $cantidad_rango_maxima um_minima $minimo_rango um_maxima $maximo_rango" >$ficherodatosaleatorios
            echo "Procesos minima $cantidad_rango_procesos_minima maxima $cantidad_rango_procesos_maxima ttl_mínima $minimo_rango_ttl ttl_maxima $maximo_rango_ttl eje_minima $minimo_rango_eje eje_maxima $maximo_rango_eje mem_minima $minimo_rango_mem mem_maxima $maximo_rango_mem" >>$ficherodatosaleatorios
            echo -ne $AMARILLO"\n¿Dónde quieres guardar los valores?"$NORMAL
            echo -ne $AMARILLO"\n1. Guardarlo en el fichero. $ficheroanteriorejecucion"$NORMAL
            echo -ne $AMARILLO"\n2. Guardarlo en otro fichero."$NORMAL
            echo -ne $AMARILLO"\n\nIntroduce una opción: "$NORMAL
            read option3

            case $option3 in
            1)

                break
                ;;

            2)
                echo -ne $AMARILLO"\nIntroduce el nombre del fichero sin extensión (Será TXT): "$NORMAL
                read nuevaruta
                break
                ;;

            *)
                #Si no se introduce una opción válida, se vuelve a mostrar el menú
                echo -ne $AMARILLO"\n\nOpción incorrecta"$NORMAL
                break
                ;;

            esac
            break
            ;;

        2)
            echo -ne $AMARILLO"\nIntroduce el nombre del fichero sin extensión (Será TXT): "$NORMAL
            read nuevaruta

            echo -ne $AMARILLO"\n¿Dónde quieres guardar los valores?"$NORMAL
            echo -ne $AMARILLO"\n1. Guardarlo en el fichero. $ficheroanteriorejecucion"$NORMAL
            echo -ne $AMARILLO"\n2. Guardarlo en otro fichero."$NORMAL
            echo -ne $AMARILLO"\n\nIntroduce una opción: "$NORMAL
            read option3

            case $option3 in
            1)

                break
                ;;

            2)
                echo -ne $AMARILLO"\nIntroduce el nombre del fichero sin extensión (Será TXT): "$NORMAL
                read nuevaruta
                break
                ;;

            *)
                #Si no se introduce una opción válida, se vuelve a mostrar el menú
                echo -ne $AMARILLO"\n\nOpción incorrecta"$NORMAL
                break
                ;;

            esac
            break
            ;;
        *)
            #Si no se introduce una opción válida, se vuelve a mostrar el menú
            echo -ne $ROJO"\n\nOpción incorrecta"$NORMAL
            break
            ;;

        esac

    done

    echo -ne $ROJO"\nPulsa ENTER para continuar "$NORMAL
    read enterContinuar
}

################################################################################################################################################################################################
# Sinopsis:   función que permite introducir las particiones indicando un rango en el fichero
################################################################################################################################################################################################

function entradaParticionesRangoManual {
    clear

    #Menu con case 3 opciones, la primera opcion indica si queremos guardar los rangos en datosrangos.txt, la segunda opcion si queremos guardar los valores aleatorios en Datos.txt y la tercera si queremos salir

}

################################################################################################################################################################################################
# Sinopsis:   función que permite  introducir los procesos por teclado
################################################################################################################################################################################################

function entradaProcesosRangoManual {

    cantidad_rango_procesos=$(shuf -i $cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima -n 1)
    llegada2=$(shuf -i $minimo_rango_ttl-$maximo_rango_ttl -n $cantidad_rango_procesos)
    tiempo2=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n $cantidad_rango_procesos)
    memoria2=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n $cantidad_rango_procesos)

    echo ""
    #Cogemos los procesos que vamos a ejecutar y los guardamos en nuestro vector
    for ((p = 1; p <= $cantidad_rango_procesos; p++)); do
        if [ $p -gt 9 ]; then
            proceso[$p]=$(echo P$(($p)))
        else
            proceso[$p]=$(echo P0$(($p)))
        fi
        llegada[$p]=$(shuf -i $minimo_rango_ttl-$maximo_rango_ttl -n 1)
        tiempo[$p]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm

            fi
        done

        if [[ ${memoria[$p]} -gt ${particiones[$aux]} ]]; then
            memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)
            if [[ ${memoria[$p]} -gt ${particiones[$aux]} ]]; then
                memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)
                if [[ ${memoria[$p]} -gt ${particiones[$aux]} ]]; then
                    memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)
                fi
            fi
        fi

        if [ $p == 1 ]; then
            if [ $opcion == '2' ]; then
                if [ $option3 == '2' ]; then
                    echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]} >>./FDatos/$nuevaruta
                fi
                if [ $option3 == '1' ]; then
                    echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]} >>$ficheroanteriorejecucion
                fi
            fi
            #echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]}  >> $ficherodatosaleatorios
            echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]}
        else
            if [ $opcion == '2' ]; then
                if [ $option3 == '2' ]; then
                    echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]} >>./FDatos/$nuevaruta
                fi
                if [ $option3 == '1' ]; then
                    echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]} >>$ficheroanteriorejecucion
                fi
            fi
            #echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]}  >> $ficherodatosaleatorios
            echo Proceso $p Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]}
        fi

    done
    echo -ne $ROJO"\nPulsa ENTER para continuar "$NORMAL
    read enterContinuar

}

################################################################################################################################################################################################
# Sinopsis:   función que permite  introducir los procesos por teclado
################################################################################################################################################################################################

function entradaProcesosRangoManual_pruebas {
    clear
    echo "¿Dónde quieres guardar los valores?"
    echo "1. Guardar los valores en el fichero de última ejecución ($ficheroanteriorejecucion)"
    echo "2. Guardar en otro fichero de valores"
    read option_guardado2
    if [ $option_guardado2 == '2' ]; then
        echo "Introduce el nombre del fichero de valores sin extensión (Será TXT): "
        read nuevaruta2
    else
        nuevaruta2="datos"
    fi
    clear

    cantidad_particiones=$(shuf -i $cantidad_rango_minima-$cantidad_rango_maxima -n 1)

    clear
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [#-#]: 0"
    echo -ne "\nNúmero de procesos procesos [#-#]: 0 "
    echo -ne "\nTiempos de llegadas de los procesos [#-#]: 0 "
    echo -ne "\nTiempos de ejecución de los procesos [#-#]: 0 "
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"

    clear
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        particiones[$contadorParticiones]=$(shuf -i $minimo_rango-$maximo_rango -n 1)
        echo -ne "${particiones[$contadorParticiones]} "
        echo "Particion $contadorParticiones ${particiones[$contadorParticiones]}" >>$ficheroanteriorejecucion
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\nNúmero de procesos procesos [#-#]: 0 "
    echo -ne "\nTiempos de llegadas de los procesos [#-#]: 0 "
    echo -ne "\nTiempos de ejecución de los procesos [#-#]: 0 "
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    clear
    contadorParticiones=1
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    cantidad_rango_procesos=$(shuf -i $cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima -n 1)
    procesitos=$cantidad_rango_procesos
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\nTiempos de llegadas de los procesos [#-#]: 0 "
    echo -ne "\nTiempos de ejecución de los procesos [#-#]: 0 "
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"

    clear
    contadorParticiones=1
    for ((i = 1; i <= $procesitos; i++)); do
        llegada[$i]=$(shuf -i $minimo_rango_ttl-$maximo_rango_ttl -n 1)
    done
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\nTiempos de llegadas de los procesos [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    clear
    contadorParticiones=1

    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    for ((i = 1; i <= $procesitos; i++)); do
        tiempo[$i]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        until [ ${tiempo[$i]} -ge 0 ]; do
            tiempo[$i]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        done
    done

    echo -ne "\nTiempos de llegadas de los procesos [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\nTiempos de ejecución de los procesos [$minimo_rango_eje-$maximo_rango_eje]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${tiempo[$i]} "
    done
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos:$NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos:$NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos:$NORMAL $minimo_rango_eje"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de ejecución de los procesos:$NORMAL $maximo_rango_eje"
    echo -ne $AMARILLO"\nMinimo del rango de unidades de memoria de los procesos: "$NORMAL
    echo -ne $AMARILLO"Máximo del rango de unidades de memoria de los procesos (Tiene que ser menor a $maximo_rango): "$NORMAL
    cantidad_procesos_rango=$cantidad_rango_procesos

    while [ $masprocesos == "s" ]; do # mientras que contador sea menor que cantidad de procesos
        clear
        if [ $p -gt 9 ]; then
            echo -ne "\n${colores[($i % 6)]}PROCESO P$(($p))\e[0m"
            proceso[$p]=$(echo P$(($p)))
        else
            echo -ne "\n${colores[($i % 6)]}PROCESO P0$(($p))\e[0m"
            proceso[$p]=$(echo P0$(($p)))
        fi
        # bloque para introduccion del resto de datos del proceso

        memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm
            fi
        done

        while [ ${memoria[$p]} -le 0 -o ${memoria[$p]} -gt ${particiones[$aux]} ]; do
            memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)
        done
        clear

        #restar -1 a cantidad_rango_procesos
        cantidad_rango_procesos=$(($cantidad_rango_procesos - 1))

        if [ $cantidad_rango_procesos -gt 0 ]; then
            masprocesos='s'
        else
            masprocesos='n'
        fi
        p=$(expr $p + 1) #incremento el contador
    done
    clear
    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        # Particion 1 30

        let contadorParticiones=$contadorParticiones+1
    done

    # Llegada 4 Ejecución 30 Memoria 8
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\nTiempos de llegadas de los procesos [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\nTiempos de ejecución de los procesos [$minimo_rango_eje-$maximo_rango_eje]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${tiempo[$i]} "
    done
    echo -ne "\nUnidades de memoria de los procesos [$minimo_rango_mem-$maximo_rango_mem]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${memoria[$i]} "
    done

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos:$NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos:$NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos:$NORMAL $minimo_rango_eje"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de ejecución de los procesos:$NORMAL $maximo_rango_eje"
    echo -ne $AMARILLO"\nMinimo del rango de unidades de memoria de los procesos:$NORMAL $minimo_rango_mem"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de los procesos (Tiene que ser menor a $maximo_rango):$NORMAL $maximo_rango_mem"

    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "Particion $contadorParticiones ${particiones[$contadorParticiones]}\n" >>./FDatos/$nuevaruta2.txt
        let contadorParticiones=$contadorParticiones+1
    done
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "Llegada ${llegada[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Ejecución ${tiempo[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Memoria ${memoria[$i]}\n" >>./FDatos/$nuevaruta2.txt
    done

    for ((j = ${#llegada[@]}; j > 0; j--)); do
        for ((i = 0; i < j; i++)); do
            if [[ ${llegada[$i]} -gt ${llegada[$(($i + 1))]} ]]; then
                aux=${llegada[$(($i + 1))]}
                llegada[$(($i + 1))]=${llegada[$i]}
                llegada[$i]=$aux

                aux=${tiempo[$(($i + 1))]}
                tiempo[$(($i + 1))]=${tiempo[$i]} #para ordenar los tiempos de ejecucion con sus tiempos de respuesta
                tiempo[$i]=$aux

                aux=${proceso[$(($i + 1))]}
                proceso[$(($i + 1))]=${proceso[$i]} #para ordenar los nombres con sus mismos valores
                proceso[$i]=$aux

                #         aux=${memoria[$(($i+1))]};
                #         memoria[$(($i+1))]=${memoria[$i]};  #para ordenar la memoria con sus mismos valores
                #         memoria[$i]=$aux;

                #aux=${colores[($(($i+1)) % 6)]};
                #colores[$(($i+1))]=${colores[($i % 6)]}
                #colores[$i]=$aux;

                #aux=${colores2[($(($i+1)) % 6)]};
                #colores2[$(($i+1))]=${colores2[($i % 6)]}
                #colores2[$i]=$aux;
            fi
        done
    done
    #guardado
}

################################################################################################################################################################################################
# Sinopsis:   función que permite  introducir los procesos por teclado
################################################################################################################################################################################################

function entradaProcesosRangoManual_op_cuatro {
    clear
    echo "¿Dónde quieres guardar los rangos?"
    echo "1. Guardar los rangos en el fichero de última ejecución ($ficherodatosaleatorios)"
    echo "2. Guardar en otro fichero de rangos"
    read option_guardado
    if [ $option_guardado == '2' ]; then
        echo "Introduce el nombre del fichero de rangos sin extensión (Será TXT): "
        read nuevaruta
    fi
    echo "¿Dónde quieres guardar los valores?"
    echo "1. Guardar los valores en el fichero de última ejecución ($ficheroanteriorejecucion)"
    echo "2. Guardar en otro fichero de valores"
    read option_guardado2
    if [ $option_guardado2 == '2' ]; then
        echo "Introduce el nombre del fichero de valores sin extensión (Será TXT): "
        read nuevaruta2
    else
        nuevaruta2="datos"
    fi
    clear
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                | [#-#]: 0"
    echo -ne "\n| Tamaño de las particiones            | [#-#]: 0"
    echo -ne "\n| Número de procesos procesos          | [#-#]: 0 "
    echo -ne "\n| Tiempos de llegadas de los procesos  | [#-#]: 0 "
    echo -ne "\n| Tiempos de ejecución de los procesos | [#-#]: 0 "
    echo -ne "\n| Unidades de memoria de los procesos  | [#-#]: 0 \n"
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones: "$NORMAL
    read cantidad_rango_minima
    echo -ne $AMARILLO"Máximo del rango del número de particiones: "$NORMAL
    read cantidad_rango_maxima
    cantidad_particiones=$(shuf -i $cantidad_rango_minima-$cantidad_rango_maxima -n 1)

    clear
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                | [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\n| Tamaño de las particiones            | [#-#]: 0"
    echo -ne "\n| Número de procesos procesos          | [#-#]: 0 "
    echo -ne "\n| Tiempos de llegadas de los procesos  | [#-#]: 0 "
    echo -ne "\n| Tiempos de ejecución de los procesos | [#-#]: 0 "
    echo -ne "\n| Unidades de memoria de los procesos  | [#-#]: 0 \n"
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: "$NORMAL
    read minimo_rango
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango): "$NORMAL
    read maximo_rango

    clear
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                | [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\n| Tamaño de las particiones            | [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        particiones[$contadorParticiones]=$(shuf -i $minimo_rango-$maximo_rango -n 1)
        echo -ne "${particiones[$contadorParticiones]} "
        echo "Particion $contadorParticiones ${particiones[$contadorParticiones]}" >>$ficheroanteriorejecucion
        let contadorParticiones=$contadorParticiones+1
    done

    echo -ne "\n| Número de procesos                   | [#-#]: 0 "
    echo -ne "\n| Tiempos de llegadas de los procesos  | [#-#]: 0 "
    echo -ne "\n| Tiempos de ejecución de los procesos | [#-#]: 0 "
    echo -ne "\n| Unidades de memoria de los procesos  | [#-#]: 0 \n"
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos: "$NORMAL
    read cantidad_rango_procesos_minima
    echo -ne $AMARILLO"Máximo del rango del número de procesos: "$NORMAL
    read cantidad_rango_procesos_maxima

    clear
    contadorParticiones=1
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                | [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\n| Tamaño de las particiones            | [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    cantidad_rango_procesos=$(shuf -i $cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima -n 1)
    procesitos=$cantidad_rango_procesos

    echo -ne "\n| Número de procesos procesos          | [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\n| Tiempos de llegadas de los procesos  | [#-#]: 0 "
    echo -ne "\n| Tiempos de ejecución de los procesos | [#-#]: 0 "
    echo -ne "\n| Unidades de memoria de los procesos  | [#-#]: 0 \n"
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos: "$NORMAL
    read minimo_rango_ttl
    echo -ne $AMARILLO"Máximo del rango del tiempo de llegada de los procesos: "$NORMAL
    read maximo_rango_ttl

    clear
    contadorParticiones=1
    for ((i = 1; i <= $procesitos; i++)); do
        llegada[$i]=$(shuf -i $minimo_rango_ttl-$maximo_rango_ttl -n 1)
    done
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                  | [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\n| Tamaño de las particiones              | [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done

    echo -ne "\n| Número de procesos                     | [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\n| Tiempos de llegadas de los procesos    | [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\n| Tiempos de ejecución de los procesos   | [#-#]: 0 "
    echo -ne "\n| Unidades de memoria de los procesos    | [#-#]: 0 \n"
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos: $NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos: $NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos: "$NORMAL
    read minimo_rango_eje
    echo -ne $AMARILLO"Máximo del rango del tiempo de ejecución de los procesos: "$NORMAL
    read maximo_rango_eje

    clear
    contadorParticiones=1
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                 | [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\n| Tamaño de las particiones             | [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\n| Número de procesos procesos           | [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    for ((i = 1; i <= $procesitos; i++)); do
        tiempo[$i]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        until [ ${tiempo[$i]} -ge 0 ]; do
            tiempo[$i]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        done
    done

    echo -ne "\n| Tiempos de llegadas de los procesos   | [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\n| Tiempos de ejecución de los procesos  | [$minimo_rango_eje-$maximo_rango_eje]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${tiempo[$i]} "
    done
    echo -ne "\n| Unidades de memoria de los procesos   | [#-#]: 0 \n"
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos:$NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos:$NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos:$NORMAL $minimo_rango_eje"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de ejecución de los procesos:$NORMAL $maximo_rango_eje"
    echo -ne $AMARILLO"\nMinimo del rango de unidades de memoria de los procesos: "$NORMAL
    read minimo_rango_mem
    echo -ne $AMARILLO"Máximo del rango de unidades de memoria de los procesos (Tiene que ser menor a $maximo_rango): "$NORMAL
    read maximo_rango_mem

    cantidad_procesos_rango=$cantidad_rango_procesos

    while [ $masprocesos == "s" ]; do # mientras que contador sea menor que cantidad de procesos
        clear
        if [ $p -gt 9 ]; then
            echo -ne "\n${colores[($i % 6)]}PROCESO P$(($p))\e[0m"
            proceso[$p]=$(echo P$(($p)))
        else
            echo -ne "\n${colores[($i % 6)]}PROCESO P0$(($p))\e[0m"
            proceso[$p]=$(echo P0$(($p)))
        fi
        # bloque para introduccion del resto de datos del proceso

        memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm
            fi
        done

        while [ ${memoria[$p]} -le 0 -o ${memoria[$p]} -gt ${particiones[$aux]} ]; do
            memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)
        done
        clear

        #restar -1 a cantidad_rango_procesos
        cantidad_rango_procesos=$(($cantidad_rango_procesos - 1))

        if [ $cantidad_rango_procesos -gt 0 ]; then
            masprocesos='s'
        else
            masprocesos='n'
        fi
        p=$(expr $p + 1) #incremento el contador
    done
    clear
    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    echo -ne "|----------------------------------------------------"
    echo -ne "\n| Número de particiones                | [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\n| Tamaño de las particiones            | [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        # Particion 1 30

        let contadorParticiones=$contadorParticiones+1
    done

    # Llegada 4 Ejecución 30 Memoria 8
    echo -ne "\n| Número de procesos                   | [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\n| Tiempos de llegadas de los procesos  |[$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\n| Tiempos de ejecución de los procesos |[$minimo_rango_eje-$maximo_rango_eje]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${tiempo[$i]} "
    done
    echo -ne "\n| Unidades de memoria de los procesos  |[$minimo_rango_mem-$maximo_rango_mem]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${memoria[$i]} "
    done
    echo -ne "|----------------------------------------------------"

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos:$NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos:$NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos:$NORMAL $minimo_rango_eje"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de ejecución de los procesos:$NORMAL $maximo_rango_eje"
    echo -ne $AMARILLO"\nMinimo del rango de unidades de memoria de los procesos:$NORMAL $minimo_rango_mem"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de los procesos (Tiene que ser menor a $maximo_rango):$NORMAL $maximo_rango_mem"

    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "Particion $contadorParticiones ${particiones[$contadorParticiones]}\n" >>./FDatos/$nuevaruta2.txt
        let contadorParticiones=$contadorParticiones+1
    done
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "Llegada ${llegada[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Ejecución ${tiempo[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Memoria ${memoria[$i]}\n" >>./FDatos/$nuevaruta2.txt
    done

    for ((j = ${#llegada[@]}; j > 0; j--)); do
        for ((i = 0; i < j; i++)); do
            if [[ ${llegada[$i]} -gt ${llegada[$(($i + 1))]} ]]; then
                aux=${llegada[$(($i + 1))]}
                llegada[$(($i + 1))]=${llegada[$i]}
                llegada[$i]=$aux

                aux=${tiempo[$(($i + 1))]}
                tiempo[$(($i + 1))]=${tiempo[$i]} #para ordenar los tiempos de ejecucion con sus tiempos de respuesta
                tiempo[$i]=$aux

                aux=${proceso[$(($i + 1))]}
                proceso[$(($i + 1))]=${proceso[$i]} #para ordenar los nombres con sus mismos valores
                proceso[$i]=$aux

                #         aux=${memoria[$(($i+1))]};
                #         memoria[$(($i+1))]=${memoria[$i]};  #para ordenar la memoria con sus mismos valores
                #         memoria[$i]=$aux;

                #aux=${colores[($(($i+1)) % 6)]};
                #colores[$(($i+1))]=${colores[($i % 6)]}
                #colores[$i]=$aux;

                #aux=${colores2[($(($i+1)) % 6)]};
                #colores2[$(($i+1))]=${colores2[($i % 6)]}
                #colores2[$i]=$aux;
            fi
        done
    done
    ##################
    #guardado
    ##################
    case $option_guardado in
    1)
        echo -ne "\nParticion minima $cantidad_rango_minima maxima $cantidad_rango_maxima um_minima $minimo_rango um_maxima $maximo_rango" >$ficherodatosaleatorios
        echo -ne "\nProcesos minima $cantidad_rango_procesos_minima maxima $cantidad_rango_procesos_maxima ttl_mínima $minimo_rango_ttl ttl_maxima $maximo_rango_ttl eje_minima $minimo_rango_eje eje_maxima $maximo_rango_eje mem_minima $minimo_rango_mem mem_maxima $maximo_rango_mem\n" >>$ficherodatosaleatorios
        return
        ;;

    2)
        echo -ne "\nParticion minima $cantidad_rango_minima maxima $cantidad_rango_maxima um_minima $minimo_rango um_maxima $maximo_rango" >./FRangos/$nuevaruta.txt
        echo -ne "\nProcesos minima $cantidad_rango_procesos_minima maxima $cantidad_rango_procesos_maxima ttl_mínima $minimo_rango_ttl ttl_maxima $maximo_rango_ttl eje_minima $minimo_rango_eje eje_maxima $maximo_rango_eje mem_minima $minimo_rango_mem mem_maxima $maximo_rango_mem\n" >>./FRangos/$nuevaruta.txt
        return
        ;;
    esac
}

###############################################################
###############################################################
## Funcion rangos aleatorios maximos
####################################################
######################################################
##########################################################

function entradaProcesosRangoManual_op_siete {

    clear
    #echo "¿Dónde quieres guardar los rangos?"
    #echo "1. Guardar los rangos en el fichero por defecto ($ficherorangos_totales)"
    #echo "2. Guardar en otro fichero de valores"
    #read option_guardado3
    #if [ $option_guardado3 == '2' ]
    #then
    #echo "Introduce el nombre del fichero de rangos sin extensión (Será TXT): "
    # read nuevaruta3
    #else
    #  nuevaruta3="datos"
    # fi

    echo "¿Dónde quieres guardar los subrangos?"
    echo "1. Guardar los subrangos en ($ficherosubrangos_totales)"
    echo "2. Guardar en otro fichero de rangos"
    read option_guardado3

    if [ $option_guardado3 == '2' ]; then
        echo "Introduce el nombre del fichero de valores sin extensión (Será TXT): "
        read nuevaruta1
    fi

    echo "¿Dónde quieres guardar los valores?"
    echo "1. Guardar los valores en el fichero por defecto (./FDatos/DatosDefault.txt)"
    echo "2. Guardar en otro fichero de valores"
    read option_guardado2
    if [ $option_guardado2 == '2' ]; then
        echo "Introduce el nombre del fichero de valores sin extensión (Será TXT): "
        read nuevaruta2
    else
        truncate -s 0 $ficheroanteriorejecucion
        nuevaruta2="datos"
    fi

    clear

    while [ $cantidad_particiones_max -le $cantidad_particiones_min ]; do
        cantidad_particiones_min=$((RANDOM % ($cantidad_rango_maxima - $cantidad_rango_minima + 1) + $cantidad_rango_minima))
        cantidad_particiones_max=$((RANDOM % ($cantidad_rango_maxima - $cantidad_rango_minima + 1) + $cantidad_rango_minima))
    done

    while [ $particiones_max -le $particiones_min ]; do
        particiones_min=$((RANDOM % ($maximo_rango - $minimo_rango + 1) + $minimo_rango))
        particiones_max=$((RANDOM % ($maximo_rango - $minimo_rango + 1) + $minimo_rango))
    done

    while [ $cantidad_rango_procesos_max -le $cantidad_rango_procesos_min ]; do
        cantidad_rango_procesos_min=$((RANDOM % ($cantidad_rango_procesos_maxima - $cantidad_rango_procesos_minima + 1) + $cantidad_rango_procesos_minima))
        cantidad_rango_procesos_max=$((RANDOM % ($cantidad_rango_procesos_maxima - $cantidad_rango_procesos_minima + 1) + $cantidad_rango_procesos_minima))
    done

    while [ $llegada_max -le $llegada_min ]; do
        llegada_min=$((RANDOM % ($maximo_rango_ttl - $minimo_rango_ttl + 1) + $minimo_rango_ttl))
        llegada_max=$((RANDOM % ($maximo_rango_ttl - $minimo_rango_ttl + 1) + $minimo_rango_ttl))
    done

    while [ $tiempo_max -le $tiempo_min ]; do
        tiempo_min=$((RANDOM % ($maximo_rango_eje - $minimo_rango_eje + 1) + $minimo_rango_eje))
        tiempo_max=$((RANDOM % ($maximo_rango_eje - $minimo_rango_eje + 1) + $minimo_rango_eje))
    done

    while [ $memoria_max -le $memoria_min ]; do
        memoria_min=$((RANDOM % ($maximo_rango_mem - $minimo_rango_mem + 1) + $minimo_rango_mem))
        memoria_max=$((RANDOM % ($maximo_rango_mem - $minimo_rango_mem + 1) + $minimo_rango_mem))
    done

    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt

    printf "\n\n"
    printf " ┌────────────────────┬─────────────┬────────────┬────────────┐\n"
    printf " │       Texto        │    AleT     │   Rangos   │   Datos    │\n"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │   NºParticiones    │   %-*s  │   %-*s  │     %-*s │\n" 8 "$cantidad_rango_minima|$cantidad_rango_maxima" 7 "$cantidad_particiones_min|$cantidad_particiones_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Tamaño Particiones │   %-*s  │   %-*s  │    %-*s  │\n" 8 "$minimo_rango|$maximo_rango" 7 "$particiones_min|$particiones_max" 8 " ─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Número de procesos │   %-*s  │   %-*s  │     %-*s │\n" 8 "$cantidad_rango_procesos_minima|$cantidad_rango_procesos_maxima" 7 "$cantidad_rango_procesos_min|$cantidad_rango_procesos_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Tiempos de llegada │   %-*s  │   %-*s  │     %-*s │\n" 8 "$minimo_rango_ttl|$maximo_rango_ttl" 7 "$llegada_min|$llegada_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │Tiempos de ejecución│   %-*s  │   %-*s  │     %-*s │\n" 8 "$minimo_rango_eje|$maximo_rango_eje" 7 "$tiempo_min|$tiempo_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │Unidades de memoria │   %-*s  │   %-*s  │     %-*s │\n" 8 "$minimo_rango_mem|$maximo_rango_mem" 7 "$memoria_min|$memoria_max" 8 "─"
    printf " └────────────────────┴─────────────┴────────────┴────────────┘\n"
    printf "\n\n"

    echo -e "$ROJO\nPulsa ENTER para continuar $NORMAL"
    read -r enterContinuar

    #
    #
    #
    #Comprobacion de errores
    #
    #
    #
    if [ $cantidad_particiones_min -lt 1 ]; then
        cantidad_particiones_min=1
        #cpartmin="$AMARILLO Se ha modificado el valor de la cantidad de particiones mínima porque tenía un valor no posible "
        cambionumerss=true
    fi

    if [ $cantidad_particiones_max -lt 1 ]; then
        cantidad_particiones_max=1
        #cpartmax="$AMARILLO Se ha modificado el valor de la cantidad de particiones máxima porque tenía un valor no posible "
        cambionumerss=true
    fi

    if [ $particiones_min -lt 1 ]; then
        particiones_min=1
        #ptmin="$AMARILLO Se ha modificado el valor del tamaño de las particiones mínimo porque tenía un valor no posible "
        cambionumerss=true
    fi

    if [ $particiones_max -lt 1 ]; then
        particiones_max=1
        #ptmax="$AMARILLO Se ha modificado el valor del tamaño de las particiones máximo porque tenía un valor no posible "
        cambionumerss=true
    fi

    if [ $cantidad_rango_procesos_min -lt 1 ]; then
        cantidad_rango_procesos_min=1
        #nprocmin="$AMARILLO Se ha modificado el valor del número de procesos mínimo porque tenía un valor no posible "
        cambionumerss=true
    fi

    if [ $cantidad_rango_procesos_max -lt 1 ]; then
        cantidad_rango_procesos_max=1
        #nprocmax="$AMARILLO Se ha modificado el valor del número de procesos máximo porque tenía un valor no posible "
        cambionumerss=true
    fi

    if [ $llegada_min -lt 0 ]; then
        llegada_min=0
        #llgmin="$AMARILLO Se ha modificado el valor de los tiempos de llegada mínimos porque tenían un valor no posible "
        cambionumerss=true
    fi

    if [ $llegada_max -lt 0 ]; then
        llegada_max=0
        #llgmax="Se ha modificado el valor de los tiempos de llegada máximos porque tenían un valor no posible "
        cambionumerss=true
    fi

    if [ $tiempo_min -lt 1 ]; then
        tiempo_min=1
        #ejecmin="Se ha modificado el valor de los tiempos de ejecución mínimos porque tenían un valor no posible "
        cambionumerss=true
    fi

    if [ $tiempo_max -lt 1 ]; then
        tiempo_max=1
        #ejecmax="Se ha modificado el valor de los tiempos de ejecución máximos porque tenían un valor no posible "
        cambionumerss=true
    fi

    if [ $memoria_min -lt 1 ]; then
        memoria_min=1
        #memomin="Se ha modificado el valor de las unidades de memoria mínimas porque tenían un valor no posible "
        cambionumerss=true
    fi

    if [ $memoria_max -lt 1 ]; then
        memoria_max=1
        #memomax="Se ha modificado el valor de las unidades de memoria máximas porque tenían un valor no posible "
        cambionumerss=true
    fi

    printf "\n\n"
    printf " ┌────────────────────┬─────────────┬────────────┬────────────┐\n"
    printf " │       Texto        │    AleT     │   Rangos   │   Datos    │\n"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │   NºParticiones    │   %-*s  │   %-*s  │     %-*s │\n" 8 "$cantidad_rango_minima|$cantidad_rango_maxima" 7 "$cantidad_particiones_min|$cantidad_particiones_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Tamaño Particiones │   %-*s  │   %-*s  │    %-*s  │\n" 8 "$minimo_rango|$maximo_rango" 7 "$particiones_min|$particiones_max" 8 " ─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Número de procesos │   %-*s  │   %-*s  │     %-*s │\n" 8 "$cantidad_rango_procesos_minima|$cantidad_rango_procesos_maxima" 7 "$cantidad_rango_procesos_min|$cantidad_rango_procesos_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Tiempos de llegada │   %-*s  │   %-*s  │     %-*s │\n" 8 "$minimo_rango_ttl|$maximo_rango_ttl" 7 "$llegada_min|$llegada_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │Tiempos de ejecución│   %-*s  │   %-*s  │     %-*s │\n" 8 "$minimo_rango_eje|$maximo_rango_eje" 7 "$tiempo_min|$tiempo_max" 8 "─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │Unidades de memoria │   %-*s  │   %-*s  │     %-*s │\n" 8 "$minimo_rango_mem|$maximo_rango_mem" 7 "$memoria_min|$memoria_max" 8 "─"
    printf " └────────────────────┴─────────────┴────────────┴────────────┘\n"
    printf "\n\n"

    if [ $cambionumerss = true ]; then
        echo $AMARILLO"Se han cambiado todos los valores que no eran posibles para la correcta ejecución"$NORMAL
    fi

    #echo -ne $AMARILLO"$cpartmin\n"$NORMAL
    #echo -ne $AMARILLO"$cpartmax\n"$NORMAL
    #echo -ne $AMARILLO"$ptmin\n"$NORMAL
    #echo -ne $AMARILLO"$ptmax\n"$NORMAL
    #echo -ne $AMARILLO"$nprocmin\n"$NORMAL
    #echo -ne $AMARILLO"$nprocmax\n"$NORMAL
    #echo -ne $AMARILLO"$llgmin\n"$NORMAL
    #echo -ne $AMARILLO"$llgmax\n"$NORMAL
    #echo -ne $AMARILLO"$ejecmin\n"$NORMAL
    #echo -ne $AMARILLO"$ejecmax\n"$NORMAL
    #echo -ne $AMARILLO"$memomin\n"$NORMAL
    #echo -ne $AMARILLO"$memomax\n"$NORMAL

    echo -e "$ROJO\nPulsa ENTER para continuar $NORMAL"
    read -r enterContinuar

    cantidad_particiones=$(shuf -i $cantidad_particiones_min-$cantidad_particiones_max -n 1)
    for ((i = 0; i < $cantidad_particiones; i++)); do
        particiones[$contadorParticiones]=$(shuf -i $particiones_min-$particiones_max -n 1)
        echo "Particion $contadorParticiones ${particiones[$contadorParticiones]}" >>$ficheroanteriorejecucion
        let contadorParticiones=$contadorParticiones+1
    done

    contadorParticiones=1

    cantidad_rango_procesos=$(shuf -i $cantidad_rango_procesos_min-$cantidad_rango_procesos_max -n 1)
    procesitos=$cantidad_rango_procesos

    contadorParticiones=1
    for ((i = 1; i <= $procesitos; i++)); do
        llegada[$i]=$(shuf -i $llegada_min-$llegada_max -n 1)
    done
    for ((i = 1; i <= $procesitos; i++)); do
        tiempo[$i]=$(shuf -i $tiempo_min-$tiempo_max -n 1)
        until [ ${tiempo[$i]} -ge 0 ]; do
            tiempo[$i]=$(shuf -i $tiempo_min-$tiempo_max -n 1)
        done
    done

    while [ $masprocesos == "s" ]; do # mientras que contador sea menor que cantidad de procesos

        if [ $p -gt 9 ]; then
            #echo -ne "\n${colores[($i % 6)]}PROCESO P$(($p))\e[0m"
            proceso[$p]=$(echo P$(($p)))
        else
            #echo -ne "\n${colores[($i % 6)]}PROCESO P0$(($p))\e[0m"
            proceso[$p]=$(echo P0$(($p)))
        fi
        # bloque para introduccion del resto de datos del proceso

        memoria[$p]=$(shuf -i $memoria_min-$memoria_max -n 1)

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm
            fi
        done

        while [ ${memoria[$p]} -le 0 -o ${memoria[$p]} -gt ${particiones[$aux]} ]; do
            memoria[$p]=$(shuf -i $memoria_min-$memoria_max -n 1)
        done

        #restar -1 a cantidad_rango_procesos
        cantidad_rango_procesos=$(($cantidad_rango_procesos - 1))

        if [ $cantidad_rango_procesos -gt 0 ]; then
            masprocesos='s'
        else
            masprocesos='n'
        fi
        p=$(expr $p + 1) #incremento el contador
    done

    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt

    for ((i = 0; i < $cantidad_particiones; i++)); do
        particiones_datos+=" ${particiones[$contadorParticiones]}"
        let contadorParticiones=$contadorParticiones+1
    done
    for ((i = 0; i <= $procesitos; i++)); do
        llegadaa+="${llegada[$i]} "
    done
    for ((i = 0; i <= $procesitos; i++)); do
        eejecucion+="${tiempo[$i]} "
    done
    for ((i = 0; i <= $procesitos; i++)); do
        meemoria+="${memoria[$i]} "
    done

    printf "\n\n"
    printf " ┌────────────────────┬─────────────┬────────────┬────────────┐\n"
    printf " │       Texto        │    AleT     │   Rangos   │   Datos    │\n"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │   NºParticiones    │   %-*s  │    %-*s │    %-*s  │\n" 8 "$cantidad_rango_minima|$cantidad_rango_maxima" 7 "$cantidad_particiones_min|$cantidad_particiones_max" 6 " $cantidad_particiones"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Tamaño Particiones │   %-*s  │    %-*s │   %-*s   │\n" 8 "$minimo_rango|$maximo_rango" 7 "$particiones_min|$particiones_max" 8 "  ─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Número de procesos │   %-*s  │    %-*s │    %-*s  │\n" 8 "$cantidad_rango_procesos_minima|$cantidad_rango_procesos_maxima" 7 "$cantidad_rango_procesos_min|$cantidad_rango_procesos_max" 6 " $procesitos"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │ Tiempos de llegada │   %-*s  │    %-*s │    %-*s  │\n" 8 "$minimo_rango_ttl|$maximo_rango_ttl" 7 "$llegada_min|$llegada_max" 8 " ─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │Tiempos de ejecución│   %-*s  │    %-*s │    %-*s  │\n" 8 "$minimo_rango_eje|$maximo_rango_eje" 7 "$tiempo_min|$tiempo_max" 8 " ─"
    printf " ├────────────────────┼─────────────┼────────────┼────────────┤\n"
    printf " │Unidades de memoria │   %-*s  │    %-*s │    %-*s  │\n" 8 "$minimo_rango_mem|$maximo_rango_mem" 7 "$memoria_min|$memoria_max" 8 " ─"
    printf " └────────────────────┴─────────────┴────────────┴────────────┘\n"
    printf "\n\n"

    echo -e "$ROJO\nPulsa ENTER para continuar $NORMAL"
    read -r enterContinuar

    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "Particion $contadorParticiones ${particiones[$contadorParticiones]}\n" >>./FDatos/$nuevaruta2.txt
        let contadorParticiones=$contadorParticiones+1
    done
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "Llegada ${llegada[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Ejecución ${tiempo[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Memoria ${memoria[$i]}\n" >>./FDatos/$nuevaruta2.txt
        echo -ne "Llegada ${llegada[$i]} " >>$ficheroanteriorejecucion
        echo -ne "Ejecución ${tiempo[$i]} " >>$ficheroanteriorejecucion
        echo -ne "Memoria ${memoria[$i]}\n" >>$ficheroanteriorejecucion
        cp ./FLast/DatosLast.txt ./FDatos/DatosDefault.txt
    done

    for ((j = ${#llegada[@]}; j > 0; j--)); do
        for ((i = 0; i < j; i++)); do
            if [[ ${llegada[$i]} -gt ${llegada[$(($i + 1))]} ]]; then
                aux=${llegada[$(($i + 1))]}
                llegada[$(($i + 1))]=${llegada[$i]}
                llegada[$i]=$aux

                aux=${tiempo[$(($i + 1))]}
                tiempo[$(($i + 1))]=${tiempo[$i]} #para ordenar los tiempos de ejecucion con sus tiempos de respuesta
                tiempo[$i]=$aux

                aux=${proceso[$(($i + 1))]}
                proceso[$(($i + 1))]=${proceso[$i]} #para ordenar los nombres con sus mismos valores
                proceso[$i]=$aux

                #         aux=${memoria[$(($i+1))]};
                #         memoria[$(($i+1))]=${memoria[$i]};  #para ordenar la memoria con sus mismos valores
                #         memoria[$i]=$aux;

                #aux=${colores[($(($i+1)) % 6)]};
                #colores[$(($i+1))]=${colores[($i % 6)]}
                #colores[$i]=$aux;

                #aux=${colores2[($(($i+1)) % 6)]};
                #colores2[$(($i+1))]=${colores2[($i % 6)]}
                #colores2[$i]=$aux;
            fi
        done
    done

    ##################
    #guardado
    ##################
    case $option_guardado3 in
    1)
        echo -ne "\nParticion minima $cantidad_particiones_min maxima $cantidad_particiones_max um_minima $particiones_min um_maxima $particiones_max" >$ficherosubrangos_totales
        echo -ne "\nProcesos minima $cantidad_rango_procesos_min maxima $cantidad_rango_procesos_max ttl_mínima $llegada_min ttl_maxima $llegada_max eje_minima $tiempo_min eje_maxima $tiempo_max mem_minima $memoria_min mem_maxima $memoria_max\n" >>$ficherosubrangos_totales
        return
        ;;

    2)
        echo -ne "\nParticion minima $cantidad_particiones_min maxima $cantidad_particiones_max um_minima $particiones_min um_maxima $particiones_max" >./FRangos/$nuevaruta.txt
        echo -ne "\nProcesos minima $cantidad_rango_procesos_min maxima $cantidad_rango_procesos_max ttl_mínima $llegada_min ttl_maxima $llegada_max eje_minima $tiempo_min eje_maxima $tiempo_max mem_minima $memoria_min mem_maxima $memoria_max\n" >>./FRangos/$nuevaruta.txt
        return
        ;;
    esac

}

################################################################################################################################################################################################
# Sinopsis:   función que permite introducir las particiones indicando un rango en el fichero
################################################################################################################################################################################################

function entradaParticionesRangoFichero {
    clear

    echo -e "\n\nFICHEROS:\n$NORMAL"
    files=("./FRangos"/*)
    for i in "${!files[@]}"; do
        echo -e "$i) ${files[$i]}"
    done
    echo -e "\n"
    echo -e "$AMARILLO\n\nIntroduce el número correspondiente al fichero: $NORMAL"
    read -r numeroFichero
    FicheroParaLectura="${files[$numeroFichero]}"

    #Cogemos los datos del fichero
    cantidad_rango_minima=$(cat $FicheroParaLectura | grep "Particion" | cut -f 3 -d " ")
    cantidad_rango_maxima=$(cat $FicheroParaLectura | grep "Particion" | cut -f 5 -d " ")
    minimo_rango=$(cat $FicheroParaLectura | grep "Particion" | cut -f 7 -d " ")
    maximo_rango=$(cat $FicheroParaLectura | grep "Particion" | cut -f 9 -d " ")
    cantidad_rango_procesos_minima=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 3 -d " ")
    cantidad_rango_procesos_maxima=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 5 -d " ")
    minimo_rango_ttl=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 7 -d " ")
    maximo_rango_ttl=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 9 -d " ")
    minimo_rango_eje=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 11 -d " ")
    maximo_rango_eje=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 13 -d " ")
    minimo_rango_mem=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 15 -d " ")
    maximo_rango_mem=$(cat $FicheroParaLectura | grep "Procesos" | cut -f 17 -d " ")

    echo -ne "\nParticion minima $cantidad_rango_minima maxima $cantidad_rango_maxima um_minima $minimo_rango um_maxima $maximo_rango"
    echo -ne "\nProcesos minima $cantidad_rango_procesos_minima maxima $cantidad_rango_procesos_maxima ttl_mínima $minimo_rango_ttl ttl_maxima $maximo_rango_ttl eje_minima $minimo_rango_eje eje_maxima $maximo_rango_eje mem_minima $minimo_rango_mem mem_maxima $maximo_rango_mem"

    clear
    ################################################################################################################################################################################################
    #Menu con case 3 opciones, la primera opcion indica si queremos guardar los rangos en datosrangos.txt, la segunda opcion si queremos guardar los valores aleatorios en Datos.txt y la tercera
    #si  queremos salir
    ################################################################################################################################################################################################
    #Guardado

}

################################################################################################################################################################################################
# Sinopsis:   función que permite introducir las particiones indicando un rango en el fichero
################################################################################################################################################################################################

function entradaParticionesRangoFichero_predefinido {
    clear

    echo -ne "\nDatos cargados:"$NORMAL

    #Cogemos los datos del fichero
    cantidad_rango_minima=$(cat $ficherodatosaleatorios | grep "Particion" | cut -f 3 -d " ")
    cantidad_rango_maxima=$(cat $ficherodatosaleatorios | grep "Particion" | cut -f 5 -d " ")
    minimo_rango=$(cat $ficherodatosaleatorios | grep "Particion" | cut -f 7 -d " ")
    maximo_rango=$(cat $ficherodatosaleatorios | grep "Particion" | cut -f 9 -d " ")
    cantidad_rango_procesos_minima=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 3 -d " ")
    cantidad_rango_procesos_maxima=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 5 -d " ")
    minimo_rango_ttl=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 7 -d " ")
    maximo_rango_ttl=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 9 -d " ")
    minimo_rango_eje=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 11 -d " ")
    maximo_rango_eje=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 13 -d " ")
    minimo_rango_mem=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 15 -d " ")
    maximo_rango_mem=$(cat $ficherodatosaleatorios | grep "Procesos" | cut -f 17 -d " ")

    echo -ne "\nParticion minima $cantidad_rango_minima maxima $cantidad_rango_maxima um_minima $minimo_rango um_maxima $maximo_rango"
    echo -ne "\nProcesos minima $cantidad_rango_procesos_minima maxima $cantidad_rango_procesos_maxima ttl_mínima $minimo_rango_ttl ttl_maxima $maximo_rango_ttl eje_minima $minimo_rango_eje eje_maxima $maximo_rango_eje mem_minima $minimo_rango_mem mem_maxima $maximo_rango_mem"

    clear
    #Menu con case 3 opciones, la primera opcion indica si queremos guardar los rangos en datosrangos.txt, la segunda opcion si queremos guardar los valores aleatorios en Datos.txt y la tercera si queremos salir
    #Guardado

}

##########################################################################################################################################################
##########################################################################################################################################################
#             Sinopsis: función igual a la de arriba pero para otro fichero de datos
##########################################################################################################################################################
##########################################################################################################################################################
function entradaParticionesRangoFichero_PRED {
    clear

    echo -ne "\nDatos cargados:"$NORMAL

    #Cogemos los datos del fichero
    cantidad_rango_minima=$(cat $ficherodatosaleatorios_totales | grep "Particion" | cut -f 3 -d " ")
    cantidad_rango_maxima=$(cat $ficherodatosaleatorios_totales | grep "Particion" | cut -f 5 -d " ")
    minimo_rango=$(cat $ficherodatosaleatorios_totales | grep "Particion" | cut -f 7 -d " ")
    maximo_rango=$(cat $ficherodatosaleatorios_totales | grep "Particion" | cut -f 9 -d " ")
    cantidad_rango_procesos_minima=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 3 -d " ")
    cantidad_rango_procesos_maxima=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 5 -d " ")
    minimo_rango_ttl=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 7 -d " ")
    maximo_rango_ttl=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 9 -d " ")
    minimo_rango_eje=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 11 -d " ")
    maximo_rango_eje=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 13 -d " ")
    minimo_rango_mem=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 15 -d " ")
    maximo_rango_mem=$(cat $ficherodatosaleatorios_totales | grep "Procesos" | cut -f 17 -d " ")

    echo -ne "\nParticion minima $cantidad_rango_minima maxima $cantidad_rango_maxima um_minima $minimo_rango um_maxima $maximo_rango"
    echo -ne "\nProcesos minima $cantidad_rango_procesos_minima maxima $cantidad_rango_procesos_maxima ttl_mínima $minimo_rango_ttl ttl_maxima $maximo_rango_ttl eje_minima $minimo_rango_eje eje_maxima $maximo_rango_eje mem_minima $minimo_rango_mem mem_maxima $maximo_rango_mem"

    clear
    #Menu con case 3 opciones, la primera opcion indica si queremos guardar los rangos en datosrangos.txt, la segunda opcion si queremos guardar los valores aleatorios en Datos.txt y la tercera si queremos salir
    #Guardado

}

################################################################################################################################################################################################
# Sinopsis:   función que permite  introducir los procesos por teclado
################################################################################################################################################################################################

function entradaProcesosRangoManual_op_cinco {

    clear
    echo "¿Dónde quieres guardar los valores?"
    echo "1. Guardar los valores en el fichero de última ejecución ($ficheroanteriorejecucion)"
    echo "2. Guardar en otro fichero de valores"
    read option_guardado2
    if [ $option_guardado2 == '2' ]; then
        echo "Introduce el nombre del fichero de valores sin extensión (Será TXT): "
        read nuevaruta2
    else
        truncate -s 0 $ficheroanteriorejecucion
        nuevaruta2="datos"
    fi
    clear

    cantidad_particiones=$(shuf -i $cantidad_rango_minima-$cantidad_rango_maxima -n 1)

    clear
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [#-#]: 0"
    echo -ne "\nNúmero de procesos procesos [#-#]: 0 "
    echo -ne "\nTiempos de llegadas de los procesos [#-#]: 0 "
    echo -ne "\nTiempos de ejecución de los procesos [#-#]: 0 "
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"

    clear
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        particiones[$contadorParticiones]=$(shuf -i $minimo_rango-$maximo_rango -n 1)
        echo -ne "${particiones[$contadorParticiones]} "
        echo "Particion $contadorParticiones ${particiones[$contadorParticiones]}" >>$ficheroanteriorejecucion
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\nNúmero de procesos procesos [#-#]: 0 "
    echo -ne "\nTiempos de llegadas de los procesos [#-#]: 0 "
    echo -ne "\nTiempos de ejecución de los procesos [#-#]: 0 "
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    clear
    contadorParticiones=1
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    cantidad_rango_procesos=$(shuf -i $cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima -n 1)
    procesitos=$cantidad_rango_procesos
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\nTiempos de llegadas de los procesos [#-#]: 0 "
    echo -ne "\nTiempos de ejecución de los procesos [#-#]: 0 "
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"

    clear
    contadorParticiones=1
    for ((i = 1; i <= $procesitos; i++)); do
        llegada[$i]=$(shuf -i $minimo_rango_ttl-$maximo_rango_ttl -n 1)
    done
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\nTiempos de llegadas de los procesos [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    clear
    contadorParticiones=1

    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        let contadorParticiones=$contadorParticiones+1
    done
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    for ((i = 1; i <= $procesitos; i++)); do
        tiempo[$i]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        until [ ${tiempo[$i]} -ge 0 ]; do
            tiempo[$i]=$(shuf -i $minimo_rango_eje-$maximo_rango_eje -n 1)
        done
    done

    echo -ne "\nTiempos de llegadas de los procesos [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\nTiempos de ejecución de los procesos [$minimo_rango_eje-$maximo_rango_eje]: "
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "${tiempo[$i]} "
    done
    echo -ne "\nUnidades de memoria de los procesos [#-#]: 0 "

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos:$NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos:$NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos:$NORMAL $minimo_rango_eje"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de ejecución de los procesos:$NORMAL $maximo_rango_eje"
    echo -ne $AMARILLO"\nMinimo del rango de unidades de memoria de los procesos: "$NORMAL
    echo -ne $AMARILLO"Máximo del rango de unidades de memoria de los procesos (Tiene que ser menor a $maximo_rango): "$NORMAL
    cantidad_procesos_rango=$cantidad_rango_procesos

    while [ $masprocesos == "s" ]; do # mientras que contador sea menor que cantidad de procesos
        clear
        if [ $p -gt 9 ]; then
            echo -ne "\n${colores[($i % 6)]}PROCESO P$(($p))\e[0m"
            proceso[$p]=$(echo P$(($p)))
        else
            echo -ne "\n${colores[($i % 6)]}PROCESO P0$(($p))\e[0m"
            proceso[$p]=$(echo P0$(($p)))
        fi
        # bloque para introduccion del resto de datos del proceso

        memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm
            fi
        done

        while [ ${memoria[$p]} -le 0 -o ${memoria[$p]} -gt ${particiones[$aux]} ]; do
            memoria[$p]=$(shuf -i $minimo_rango_mem-$maximo_rango_mem -n 1)
        done
        clear

        #restar -1 a cantidad_rango_procesos
        cantidad_rango_procesos=$(($cantidad_rango_procesos - 1))

        if [ $cantidad_rango_procesos -gt 0 ]; then
            masprocesos='s'
        else
            masprocesos='n'
        fi
        p=$(expr $p + 1) #incremento el contador
    done
    clear
    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    echo -ne "Número de particiones [$cantidad_rango_minima-$cantidad_rango_maxima]: $cantidad_particiones"
    echo -ne "\nTamaño de las particiones [$minimo_rango-$maximo_rango]: "
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "${particiones[$contadorParticiones]} "
        # Particion 1 30

        let contadorParticiones=$contadorParticiones+1
    done

    # Llegada 4 Ejecución 30 Memoria 8
    echo -ne "\nNúmero de procesos procesos [$cantidad_rango_procesos_minima-$cantidad_rango_procesos_maxima]: $procesitos"
    echo -ne "\nTiempos de llegadas de los procesos [$minimo_rango_ttl-$maximo_rango_ttl]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${llegada[$i]} "
    done
    echo -ne "\nTiempos de ejecución de los procesos [$minimo_rango_eje-$maximo_rango_eje]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${tiempo[$i]} "
    done
    echo -ne "\nUnidades de memoria de los procesos [$minimo_rango_mem-$maximo_rango_mem]: "
    for ((i = 0; i <= $procesitos; i++)); do
        echo -ne "${memoria[$i]} "
    done

    echo -ne "\nInformación de la particiones"
    echo -ne $AMARILLO"\nMínimo del rango del número de particiones:$NORMAL $cantidad_rango_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de particiones:$NORMAL $cantidad_rango_maxima"
    echo -ne $AMARILLO"\nMínimo del rango de unidades de memoria de las particiones: $NORMAL $minimo_rango"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de las particiones (Tiene que ser mayor a $minimo_rango):$NORMAL $maximo_rango"
    echo -ne "\n\nInformación de los procesos"
    echo -ne $AMARILLO"\nMínimo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_minima"
    echo -ne $AMARILLO"\nMáximo del rango del número de procesos:$NORMAL $cantidad_rango_procesos_maxima"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de llegada de los procesos:$NORMAL $minimo_rango_ttl"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de llegada de los procesos:$NORMAL $maximo_rango_ttl"
    echo -ne $AMARILLO"\nMínimo del rango del tiempo de ejecución de los procesos:$NORMAL $minimo_rango_eje"
    echo -ne $AMARILLO"\nMáximo del rango del tiempo de ejecución de los procesos:$NORMAL $maximo_rango_eje"
    echo -ne $AMARILLO"\nMinimo del rango de unidades de memoria de los procesos:$NORMAL $minimo_rango_mem"
    echo -ne $AMARILLO"\nMáximo del rango de unidades de memoria de los procesos (Tiene que ser menor a $maximo_rango):$NORMAL $maximo_rango_mem"

    contadorParticiones=1
    echo "" >./FDatos/$nuevaruta2.txt
    for ((i = 0; i < $cantidad_particiones; i++)); do
        echo -ne "Particion $contadorParticiones ${particiones[$contadorParticiones]}\n" >>./FDatos/$nuevaruta2.txt
        let contadorParticiones=$contadorParticiones+1
    done
    for ((i = 1; i <= $procesitos; i++)); do
        echo -ne "Llegada ${llegada[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Ejecución ${tiempo[$i]} " >>./FDatos/$nuevaruta2.txt
        echo -ne "Memoria ${memoria[$i]}\n" >>./FDatos/$nuevaruta2.txt
        echo -ne "Llegada ${llegada[$i]} " >>$ficheroanteriorejecucion
        echo -ne "Ejecución ${tiempo[$i]} " >>$ficheroanteriorejecucion
        echo -ne "Memoria ${memoria[$i]}\n" >>$ficheroanteriorejecucion
    done

    for ((j = ${#llegada[@]}; j > 0; j--)); do
        for ((i = 0; i < j; i++)); do
            if [[ ${llegada[$i]} -gt ${llegada[$(($i + 1))]} ]]; then
                aux=${llegada[$(($i + 1))]}
                llegada[$(($i + 1))]=${llegada[$i]}
                llegada[$i]=$aux

                aux=${tiempo[$(($i + 1))]}
                tiempo[$(($i + 1))]=${tiempo[$i]} #para ordenar los tiempos de ejecucion con sus tiempos de respuesta
                tiempo[$i]=$aux

                aux=${proceso[$(($i + 1))]}
                proceso[$(($i + 1))]=${proceso[$i]} #para ordenar los nombres con sus mismos valores
                proceso[$i]=$aux

                #         aux=${memoria[$(($i+1))]};
                #         memoria[$(($i+1))]=${memoria[$i]};  #para ordenar la memoria con sus mismos valores
                #         memoria[$i]=$aux;

                #aux=${colores[($(($i+1)) % 6)]};
                #colores[$(($i+1))]=${colores[($i % 6)]}
                #colores[$i]=$aux;

                #aux=${colores2[($(($i+1)) % 6)]};
                #colores2[$(($i+1))]=${colores2[($i % 6)]}
                #colores2[$i]=$aux;
            fi
        done
    done
}

################################################################################################################################################################################################
# Sinopsis:   función que permite inrtoducir las particiones desde fichero (predefinido)
################################################################################################################################################################################################

function entradaParticionesFichero {
    clear
    echo -ne $ROJO"El formato del fichero deberá ser el siguiente: "$NORMAL
    echo -ne "\nPara que sea funcional tiene que tener particiones Por ejemplo:"
    echo -ne "\nParticion 1 30"
    echo -ne "\nParticion 2 10"
    echo -ne "\nLlegada 4 Ejecución 30 Memoria 8"
    echo -ne "\nLlegada 6 Ejecución 27 Memoria 8"
    echo -e "\n\nFICHEROS:\n$NORMAL"
    files=($(ls -l ./FDatos/ | awk '{print $9}'))
    for i in "${!files[@]}"; do
        echo -e "$i) ${files[$i]}"
    done

    echo -e "\n"
    echo -e "$AMARILLO\n\nIntroduce el número correspondiente al fichero a analizar: $NORMAL"
    read -r numeroFichero
    FicheroParaLectura="${files[$numeroFichero]}"

    lineaspart=($(cat "./FDatos/$FicheroParaLectura" | grep "Particion" | wc -l))
    for ((i = 0; i < "$lineaspart"; i++)); do
        a=($(cat "./FDatos/$FicheroParaLectura" | grep "Particion" | awk '{print $2}'))
        contadorParticiones="${a[$i]}"
        nparti=($(cat "./FDatos/$FicheroParaLectura" | grep "Particion" | awk '{print $3}'))
        echo -e "\n"
        particiones["$contadorParticiones"]="${nparti[$i]}"
        echo "Partición $contadorParticiones ${particiones[$contadorParticiones]}"
        echo "Particion $contadorParticiones ${particiones[$contadorParticiones]}" >>"$ficheroanteriorejecucion"
    done

    echo
    echo -e "$ROJO\nPulsa ENTER para continuar $NORMAL"
    read -r enterContinuar
}

################################################################################################################################################################################################
# Sinopsis:   función que permite  introducir los procesos por teclado
################################################################################################################################################################################################

function entradaProcesosTeclado {
    while [ $masprocesos == "s" ]; do # mientras que contador sea menor que cantidad de procesos
        clear
        echo $NORMAL" Ref Tll Tej Mem"
        for ((i = 1; i <= ${#proceso[@]}; i++)); do
            echo -ne " ${colores[$i % 6]}${proceso[$i]}"
            if [[ ${llegada[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${llegada[$i]}"
            elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${llegada[$i]}"
            else
                echo -ne "  ${colores[$i % 6]}${llegada[$i]}"
            fi
            if [[ ${tiempo[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${tiempo[$i]}"
            elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${tiempo[$i]}"
            else
                echo -ne "  ${colores[$i % 6]}${tiempo[$i]}"
            fi
            if [[ ${memoria[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${tiempo[$i]}"
            elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${memoria[$i]}"
            else
                echo -ne "  ${colores[$i % 6]}${memoria[$i]}"
            fi
            echo "" $NORMAL
            echo "" $NORMAL >>$informeConColor
            echo "" >>$informeSinColor
        done
        echo ""
        echo "" >>$informeConColor
        echo "" >>$informeSinColor

        #El nombre de los procesos está predefinido, por recomendación del profesor
        #antes se dejaba al usuario introducirlos, pero no es lo mejor
        if [ $p -gt 9 ]; then
            echo -ne "\n${colores[($i % 6)]}PROCESO P$(($p))\e[0m"
            echo -ne "\n${colores[($i % 6)]}PROCESO P$(($p))\e[0m" >>$informeConColor
            echo -n "\nPROCESO P$(($p))" >>$informeSinColor
            proceso[$p]=$(echo P$(($p)))
        else
            echo -ne "\n${colores[($i % 6)]}PROCESO P0$(($p))\e[0m"
            echo -ne "\n${colores[($i % 6)]}PROCESO P0$(($p))\e[0m" >>$informeConColor
            echo -ne "\nPROCESO P0$(($p))" >>$informeSinColor
            proceso[$p]=$(echo P0$(($p)))
        fi

        # bloque para introduccion del resto de datos del proceso
        echo ""
        echo "" >>$informeConColor
        echo "" >>$informeSinColor
        echo -ne "\nTiempo de llegada del proceso $p: "
        echo -ne "\nTiempo de llegada del proceso $p: " >>$informeConColor
        echo -ne "\nTiempo de llegada del proceso $p: " >>$informeSinColor
        read llegada[$p]

        echo "" >>$informeConColor
        echo "" >>$informeSinColor
        echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
        echo " Ref Tll Tej Mem" >>$informeSinColor

        for ((i = 1; i <= ${#proceso[@]}; i++)); do
            echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>$informeConColor
            echo -n " ${proceso[$i]}" >>$informeSinColor
            if [[ ${llegada[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n " ${llegada[$i]}" >>$informeSinColor
            elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n "   ${llegada[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n "  ${llegada[$i]}" >>$informeSinColor
            fi
            if [[ ${tiempo[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n " ${tiempo[$i]}" >>$informeSinColor
            elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n "   ${tiempo[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n "  ${tiempo[$i]}" >>$informeSinColor
            fi
            if [[ ${memoria[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n " ${memoria[$i]}" >>$informeSinColor
            elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n "   ${memoria[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n "  ${memoria[$i]}" >>$informeSinColor
            fi
            #echo ""
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
        done
        echo ""$NORMAL

        until [ ${llegada[$p]} -ge 0 ]; do
            echo "No se pueden introducir tiempos de llegada negativos"
            echo "No se pueden introducir tiempos de llegada negativos" >>$informeConColor
            echo "No se pueden introducir tiempos de llegada negativos" >>$informeSinColor
            echo "Introduce un nuevo tiempo de llegada"
            echo "Introduce un nuevo tiempo de llegada" >>$informeConColor
            echo "Introduce un nuevo tiempo de llegada" >>$informeSinColor
            read llegada[$p]
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
            echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
            echo " Ref Tll Tej Mem" >>$informeSinColor

            for ((i = 1; i <= ${#proceso[@]}; i++)); do
                echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>$informeConColor
                echo -n " ${proceso[$i]}" >>$informeSinColor
                if [[ ${llegada[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n " ${llegada[$i]}" >>$informeSinColor
                elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n "   ${llegada[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n "  ${llegada[$i]}" >>$informeSinColor
                fi
                if [[ ${tiempo[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n " ${tiempo[$i]}" >>$informeSinColor
                elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n "   ${tiempo[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n "  ${tiempo[$i]}" >>$informeSinColor
                fi
                if [[ ${memoria[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n " ${memoria[$i]}" >>$informeSinColor
                elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n "   ${memoria[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n "  ${memoria[$i]}" >>$informeSinColor
                fi
                #echo ""
                echo "" >>$informeConColor
                echo "" >>$informeSinColor
            done

        done
        echo ""
        echo "" $NORMAL >>$informeConColor
        echo "" >>$informeSinColor
        echo -ne "\nTiempo de ejecución del proceso $p: "
        echo -ne "\nTiempo de ejecución del proceso $p: " >>$informeConColor
        echo -ne "\nTiempo de ejecución del proceso $p: " >>$informeSinColor
        read tiempo[$p]
        echo "" >>$informeConColor
        echo "" >>$informeSinColor
        echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
        echo " Ref Tll Tej Mem" >>$informeSinColor

        for ((i = 1; i <= ${#proceso[@]}; i++)); do
            echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>$informeConColor
            echo -n " ${proceso[$i]}" >>$informeSinColor
            if [[ ${llegada[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n " ${llegada[$i]}" >>$informeSinColor
            elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n "   ${llegada[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n "  ${llegada[$i]}" >>$informeSinColor
            fi
            if [[ ${tiempo[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n " ${tiempo[$i]}" >>$informeSinColor
            elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n "   ${tiempo[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n "  ${tiempo[$i]}" >>$informeSinColor
            fi
            if [[ ${memoria[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n " ${memoria[$i]}" >>$informeSinColor
            elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n "   ${memoria[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n "  ${memoria[$i]}" >>$informeSinColor
            fi
            #echo ""
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
        done
        echo ""$NORMAL

        until [ ${tiempo[$p]} -ge 0 ]; do
            echo "No se pueden introducir tiempos de ejecución negativos"
            echo "No se pueden introducir tiempos de ejecución negativos" >>$informeConColor
            echo "No se pueden introducir tiempos de ejecución negativos" >>$informeSinColor
            echo "Introduce un nuevo tiempo de ejecución"
            echo "Introduce un nuevo tiempo de ejecución" >>$informeConColor
            echo "Introduce un nuevo tiempo de ejecución" >>$informeSinColor
            read tiempo[$p]
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
            echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
            echo " Ref Tll Tej Mem" >>$informeSinColor

            for ((i = 1; i <= ${#proceso[@]}; i++)); do
                echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>$informeConColor
                echo -n " ${proceso[$i]}" >>$informeSinColor
                if [[ ${llegada[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n " ${llegada[$i]}" >>$informeSinColor
                elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n "   ${llegada[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n "  ${llegada[$i]}" >>$informeSinColor
                fi
                if [[ ${tiempo[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n " ${tiempo[$i]}" >>$informeSinColor
                elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n "   ${tiempo[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n "  ${tiempo[$i]}" >>$informeSinColor
                fi
                if [[ ${memoria[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n " ${memoria[$i]}" >>$informeSinColor
                elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n "   ${memoria[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n "  ${memoria[$i]}" >>$informeSinColor
                fi
                #echo ""
                echo "" >>$informeConColor
                echo "" >>$informeSinColor
            done
            echo ""$NORMAL

        done
        echo ""
        echo "" $NORMAL >>$informeConColor
        echo "" >>$informeSinColor
        echo -ne "\nRáfagas de memoria del proceso $p: "
        echo -ne "\nRáfagas de memoria del proceso $p: " >>$informeConColor
        echo -ne "\nRáfagas de memoria del proceso $p: " >>$informeSinColor
        read memoria[$p]
        echo "" >>$informeConColor
        echo "" >>$informeSinColor
        echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
        echo " Ref Tll Tej Mem" >>$informeSinColor

        for ((i = 1; i <= ${#proceso[@]}; i++)); do
            echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>$informeConColor
            echo -n " ${proceso[$i]}" >>$informeSinColor
            if [[ ${llegada[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n " ${llegada[$i]}" >>$informeSinColor
            elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n "   ${llegada[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                echo -n "  ${llegada[$i]}" >>$informeSinColor
            fi
            if [[ ${tiempo[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n " ${tiempo[$i]}" >>$informeSinColor
            elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n "   ${tiempo[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                echo -n "  ${tiempo[$i]}" >>$informeSinColor
            fi
            if [[ ${memoria[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n " ${memoria[$i]}" >>$informeSinColor
            elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n "   ${memoria[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                echo -n "  ${memoria[$i]}" >>$informeSinColor
            fi
            #echo ""
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
        done
        echo ""$NORMAL
        echo ""
        echo "" >>$informeConColor
        echo "" >>$informeSinColor

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm
            fi
        done

        while [ ${memoria[$p]} -le 0 -o ${memoria[$p]} -gt ${particiones[$aux]} ]; do
            echo "No se pueden introducir memoria negativa o superior a la partición máxima"
            echo "No se pueden introducir memoria negativa o superior a la partición máxima" >>$informeConColor
            echo "No se pueden introducir memoria negativa o superior a la partición máxima" >>$informeSinColor
            echo "Introduce un nuevo tamaño de memoria"
            echo "Introduce un nuevo tamaño de memoria" >>$informeConColor
            echo "Introduce un nuevo tamaño de memoria" >>$informeSinColor
            read memoria[$p]
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
            echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
            echo " Ref Tll Tej Mem" >>$informeSinColor

            for ((i = 1; i <= ${#proceso[@]}; i++)); do
                echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>$informeConColor
                echo -n " ${proceso[$i]}" >>$informeSinColor
                if [[ ${llegada[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n " ${llegada[$i]}" >>$informeSinColor
                elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n "   ${llegada[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${llegada[$i]}" >>$informeConColor
                    echo -n "  ${llegada[$i]}" >>$informeSinColor
                fi
                if [[ ${tiempo[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n " ${tiempo[$i]}" >>$informeSinColor
                elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n "   ${tiempo[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" >>$informeConColor
                    echo -n "  ${tiempo[$i]}" >>$informeSinColor
                fi
                if [[ ${memoria[$i]} -gt 99 ]]; then
                    echo -ne " ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n " ${memoria[$i]}" >>$informeSinColor
                elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                    echo -ne "   ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n "   ${memoria[$i]}" >>$informeSinColor
                else
                    echo -ne "  ${colores[$i % 6]}${memoria[$i]}" >>$informeConColor
                    echo -n "  ${memoria[$i]}" >>$informeSinColor
                fi
                #echo ""
                echo "" >>$informeConColor
                echo "" >>$informeSinColor
            done
            echo ""$NORMAL
        done
        # salida de datos introducidos sobre procesos para que el usuario pueda ver lo que esta introducciendo y volcado de los mismos
        # en ficheros auxiliares
        echo ""
        if [[ $p -eq 1 ]]; then
            echo Llegada ${llegada[$p]} Ejecucion ${tiempo[$p]} Memoria ${memoria[$p]} >>$ficheroanteriorejecucion

        else
            echo Llegada ${llegada[$p]} Ejecucion ${tiempo[$p]} Memoria ${memoria[$p]} >>$ficheroanteriorejecucion
        fi
        clear
        echo $NORMAL" Ref Tll Tej Mem"
        echo $NORMAL" Ref Tll Tej Mem" >>$informeConColor
        echo " Ref Tll Tej Mem" >>$informeSinColor
        for ((j = ${#llegada[@]}; j > 0; j--)); do
            for ((i = 0; i < j; i++)); do
                if [[ ${llegada[$i]} -gt ${llegada[$(($i + 1))]} ]]; then
                    aux=${llegada[$(($i + 1))]}
                    llegada[$(($i + 1))]=${llegada[$i]}
                    llegada[$i]=$aux

                    aux=${tiempo[$(($i + 1))]}
                    tiempo[$(($i + 1))]=${tiempo[$i]} #para ordenar los tiempos de ejecucion con sus tiempos de respuesta
                    tiempo[$i]=$aux

                    aux=${proceso[$(($i + 1))]}
                    proceso[$(($i + 1))]=${proceso[$i]} #para ordenar los nombres con sus mismos valores
                    proceso[$i]=$aux

                    #         aux=${memoria[$(($i+1))]};
                    #         memoria[$(($i+1))]=${memoria[$i]};  #para ordenar la memoria con sus mismos valores
                    #         memoria[$i]=$aux;

                    #aux=${colores[($(($i+1)) % 6)]};
                    #colores[$(($i+1))]=${colores[($i % 6)]}
                    #colores[$i]=$aux;

                    #aux=${colores2[($(($i+1)) % 6)]};
                    #colores2[$(($i+1))]=${colores2[($i % 6)]}
                    #colores2[$i]=$aux;
                fi
            done
        done

        for ((i = 1; i <= ${#proceso[@]}; i++)); do
            echo -ne " ${colores[$i % 6]}${proceso[$i]}" | tee -a $informeConColor
            echo -n " ${proceso[$i]}" >>$informeSinColor
            if [[ ${llegada[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a $informeConColor
                echo -n " ${llegada[$i]}" >>$informeSinColor
            elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a $informeConColor
                echo -n "   ${llegada[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a $informeConColor
                echo -n "  ${llegada[$i]}" >>$informeSinColor
            fi
            if [[ ${tiempo[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a $informeConColor
                echo -n " ${tiempo[$i]}" >>$informeSinColor
            elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a $informeConColor
                echo -n "   ${tiempo[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a $informeConColor
                echo -n "  ${tiempo[$i]}" >>$informeSinColor
            fi
            if [[ ${memoria[$i]} -gt 99 ]]; then
                echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a $informeConColor
                echo -n " ${memoria[$i]}" >>$informeSinColor
            elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a $informeConColor
                echo -n "   ${memoria[$i]}" >>$informeSinColor
            else
                echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a $informeConColor
                echo -n "  ${memoria[$i]}" >>$informeSinColor
            fi
            echo ""
            echo "" >>$informeConColor
            echo "" >>$informeSinColor
        done
        echo ""$NORMAL
        echo -ne "\n¿Quieres más procesos? s/n "
        echo -ne $NORMAL"\n¿Quieres más procesos? s/n " >>$informeConColor
        echo -ne "\n¿Quieres más procesos? s/n " >>$informeSinColor
        read masprocesos
        echo "$masprocesos" >>$informeConColor
        echo "$masprocesos" >>$informeSinColor
        until [[ $masprocesos == "s" || $masprocesos == "n" ]]; do
            echo -ne "\nEscribe 's' o 'n', por favor: "
            echo -ne "\nEscribe 's' o 'n', por favor: " >>$informeConColor
            echo -ne "\nEscribe 's' o 'n', por favor: " >>$informeSinColor
            read masprocesos
            echo "$masprocesos" >>$informeConColor
            echo "$masprocesos" >>$informeSinColor
        done
        p=$(expr $p + 1) #incremento el contador
    done
}

################################################################################################################################################################################################
# Sinopsis:   función que permite introducir los procesos desde fichero (predefinido)
################################################################################################################################################################################################

function entradaProcesosFichero {
    clear

    cat $FicheroParaLectura.txt | grep "Proceso"

    llegada2=($(cat ./FDatos/$FicheroParaLectura | grep "Llegada" | cut -f 2 -d" "))
    tiempo2=($(cat ./FDatos/$FicheroParaLectura | grep "Llegada" | cut -f 4 -d" "))
    memoria2=($(cat ./FDatos/$FicheroParaLectura | grep "Llegada" | cut -f 6 -d" "))

    #Se cuentan la cantidad de procesos que hay predefinidos en un fichero
    profich=($(wc -l ./FDatos/$FicheroParaLectura | cut -f 1 -d " "))
    proficheroentrada=$(($profich - $contadorParticiones))
    echo ""
    #Cogemos los procesos que vamos a ejecutar y los guardamos en nuestro vector
    for ((p = 1; p <= $proficheroentrada; p++)); do
        if [ $p -gt 9 ]; then
            proceso[$p]=$(echo P$(($p)))
        else
            proceso[$p]=$(echo P0$(($p)))
        fi
        llegada[$p]=${llegada2[$(($p - 1))]}
        tiempo[$p]=${tiempo2[$(($p - 1))]}
        memoria[$p]=${memoria2[$(($p - 1))]}

        #Seleccionamos la particion mayor
        memMax=0
        for ((mm = 1; mm <= ${#particiones[@]}; mm++)); do
            if [[ ${particiones[$mm]} -gt $memMax ]]; then
                memMax=${particiones[$mm]}
                aux=$mm

            fi
        done

        if [[ ${memoria[$p]} -gt ${particiones[$aux]} ]]; then
            echo
            echo "Error"
            echo "La memoria tiene mayor tamaño que la partición más grande"
            echo -ne $ROJO"\nPulsa ENTER para continuar "$NORMAL
            read enterContinuar
            menuEntradaProcesos
        fi

        if [ $p == 1 ]; then
            echo Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]} >>$ficheroanteriorejecucion
        else
            echo Llegada ${llegada[$p]} Ejecución ${tiempo[$p]} Memoria ${memoria[$p]} >>$ficheroanteriorejecucion
        fi
    done
}

################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
################################################################################################################################################################################################
# Sinopsis:   función que inicializa los vectores que usaremos en el algoritmo SRPT_FNI_AjusteMejor -- ahora cambiado a FCFS-SJF_FNI_AjustePrimer
################################################################################################################################################################################################

function inicializaVectores {
    for ((i = 1; i <= ${#particiones[@]}; i++)); do
        particionOcupada[$i]=0
        procesoEnParticionOcupada[$i]=0
        ocupadas[$i]=0
    done

    for ((p = 0; p <= ${#memoria[@]}; p++)); do
        espera[$p]=0 #inicializo varios vectores con unos valores determinados
        entrada[$p]=0
        tiempoEsperaProceso[$p]=0
        restante[$p]=0
        tiempoRespuestaProceso[$p]=0
        procesoYaHaEntrado[$p]=0
        estado[$p]="Fuera del sistema"
        inicioEjecucion[$p]=0
        bandera[$p]=0
        bloqueo[$p]=0
        sale[$p]=0
    done
    procesoYaHaEntrado[0]=1

    for ((k = 0; k <= 100; k++)); do
        gantt[$k]=99
        gantt2[$k]=99
    done
}

function tiempoejecucionalgormitmo {
    echo -ne $VERDE"\n\nIntroduce una opción: \n"
    echo -ne "\n1.Ejecución por eventos. (Enters)."
    echo -ne "\n2.Ejecución automática. (Por tiempo/segundos)."
    echo -ne "\n3.Ejecución completa. (Sin pausas)\n\n"
    echo -ne "\nIntroduce una opción: "$NORMAL
    read opt2
    case $opt2 in

    1)
        optejecucion=2
        return
        ;;
    2)
        echo -ne "Introduce el tiempo entre actualizaciones de datos (segundos): "
        read tiempoejecucion
        optejecucion=3
        return
        ;;
    3)
        optejecucion=1
        return
        ;;

    *)
        echo "Opción incorrecta."
        return
        ;;
    esac
}

############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################                                                           #####################################################
############################################                         ALGORITMO SJF                     #####################################################
############################################                                                           #####################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################
############################################################################################################################################################

function algoritmoSJF_AjustePrimer {
    clear
    let "poreventos=0"; # Para conocer cuando se dispara el volcado. (Si vale 1 se ha disparado)

    evento1=0
    evento2=0
    evento3=0

    if [[ $reloj -eq 0 ]]; then
        evento3=1
    else
        evento3=0
    fi

    ############################################################################
    # Se ejecuta siempre
    ############################################################################
    let " reloj = -1 "
    # Comienzo del algoritmo de SJF con particiones distintas y ajuste mejor
    while [[ $salida != "s" ]]; do
        let " reloj = $reloj + 1  "
        ############################################################################
        # Control de Particiones y Estados de los Procesos
        ############################################################################

        for ((i = 1; i <= ${#llegada[@]}; i++)); do
            # Si el proceso no ha salido, no ocupa ninguna partición y proceso anterior ha entrado ya
            if [[ ${sale[$i]} -ne 1 && ${procesoEnParticionOcupada[$i]} -ne 1 ]]; then
                contador=0
                if [[ ${llegada[$i]} -le $reloj ]]; then # si cambio aqui llegada no va
                    # 'for' para particiones
                    for ((j = 1; j <= ${#particiones[@]}; j++)); do
                        # Si el tamaño en memoria del proceso es menor que alguna partición y ésta no está ocupada...
                        if [[ ${memoria[$i]} -le ${particiones[$j]} && ${particionOcupada[$j]} -eq 0 ]]; then
                            # ...metemos al proceso en esa partición
                            procesoEnParticionOcupada[$i]=1 # El proceso $i está en una partición ocupada
                            procesoYaHaEntrado[$i]=1        # El proceso $i ha entrado en memoria
                            entrada[$i]=$reloj
                            if [[ ${estado[$i]} != "En memoria" ]]; then # Sólo se cambia la variable "poreventos" si se ha producido una modificación en el Estado del proceso.
                                let "poreventos=1"
                            fi
                            estado[$i]="En memoria"
                            let restante[$i]=${tiempo[$i]}
                            #Buscamos el primer (antes mejor) ajuste posible con la minima diff memoria sobrante

                            diff_mem=100
                            diff=$j

                            for ((dm = 1; dm <= ${#particiones[@]}; dm++)); do
                                if [[ ${particionOcupada[$dm]} -eq 0 && ${particiones[$dm]} -ge ${memoria[$i]} ]]; then #si la posicion esta vacia y el tamaño de la posicion es mayor o igual a la memoria actual

                                    auxMem=$(expr ${particiones[$dm]} - ${memoria[$i]}) # resta entre el tamaño de la partición y el valor de la memoria correspondiente
                                fi
                                #if [[ $auxMem -lt $diff_mem && ${particionOcupada[$dm]} -eq 0 && ${particiones[$dm]} -ge ${memoria[$i]} ]]  #quitando estas lineas comentadas cambio de primer a mejor
                                #then
                                #  diff_mem=$auxMem
                                #   diff=$dm
                                #fi
                            done
                            ocupadas[$diff]=$i               # asigno a diff del array ocupadas el valor de i
                            partConProceso[$i]=$diff         # asigno el valor diff al indice i del array partConProceso
                            particionOcupada[$diff]=1        #La partición $j está ocupada    # asigno el valor 1 al indice diff del array particionOcupada
                            j=$(expr ${#particiones[@]} + 1) # asigno a j la longitud del array particiones +1
                        else
                            #...si no, si la partición estaba vacía, sigue vacía
                            if [[ ${particionOcupada[$j]} -eq 0 ]]; then
                                ((contador++))
                            fi
                        fi
                    done
                fi
            fi

            # 1) Ajustamos los estados
            if [[ ${tiempoEsperaProceso[$i]} -lt 0 && ${llegada[$i]} -ge $reloj && ${sale[$i]} -eq 0 ]]; then
                estado[$i]="Fuera del sistema"
            else
                if [[ ${procesoEnParticionOcupada[$i]} -ne 1 && ${llegada[$i]} -le $reloj && ${estado[$i]} != "Finalizado" && ${sale[$i]} -eq 0 ]]; then
                    if [[ ${estado[$i]} != "En espera" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                        # producido una modificación en el Estado del proceso.
                        let "poreventos=1"
                        #echo -ne "kkkk ssssssssssssssssssssss En espera 2060\n"
                    fi
                    estado[$i]="En espera"
                fi
            fi

            # 2)Ajustamos tiempos de respuesta segun el estado en el que nos encontramos
            if [[ ${estado[$i]} != "Finalizado" ]]; then
                let tiempoRespuestaProceso[$i]=$reloj-${llegada[$i]}
                if [[ ${tiempoRespuestaProceso[$i]} -lt 0 ]]; then
                    tiempoRespuestaProceso[$i]=0
                fi
            fi

            # 3)Si estamos en ejecución/no ejecución: ajustamos el tiempo de Espera
            if [[ ${bandera[$i]} -eq 0 && ${sale[$i]} -eq 0 ]]; then
                if [[ ${estado[$i]} != "En pausa" ]]; then
                    let tiempoEsperaProceso[$i]=${tiempoRespuestaProceso[$i]}
                else
                    let tiempoEsperaProceso[$i]=${tiempoEsperaProceso[$i]}+1
                fi
            else
                if [[ ${bandera[$i]} -eq 1 && ${sale[$i]} -eq 0 && ${bloqueo[$i]} -eq 0 ]]; then
                    let tiempoEsperaProceso[$i]=${tiempoRespuestaProceso[$i]}-$reloj+${inicioEjecucion[$i]}

                fi
            fi

            # 4)Ajustamos el tiempo restante de ejecución decrementando para el estado "En ejecución"
            if [[ ${estado[$i]} == "En ejecución" && ${sale[$i]} -eq 0 ]]; then
                let restante[$i]=${restante[$i]}-1
            fi

            #En caso de que sea el primer proceso
            if [[ $i -eq 1 && ${sale[$i]} -eq 0 && ${bloqueo[$i]} -eq 0 ]]; then

                if [[ $reloj -lt ${llegada[$i]} ]]; then
                    estado[$i]="Fuera del sistema"
                    if [[ $reloj -eq 0 ]]; then
                        evento3=1
                    else
                        evento3=0
                    fi
                else
                    if [[ ${estado[$i]} != "En ejecución" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                        # producido una modificación en el Estado del proceso.
                        let "poreventos=1"
                        #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2116\n"
                    fi
                    estado[$i]="En ejecución"
                    #gantt[$reloj]=$i
                    inicioEjecucion[$i]=$reloj
                    bandera[$i]=1
                    bloqueo[$i]=1
                    let restante[$i]=${tiempo[$i]}

                fi

            else
                for ((ct = 1; ct <= ${#particiones[@]}; ct++)); do
                    if [[ ${particionOcupada[$ct]} -eq 0 && ${llegada[$i]} -le $reloj && ${memoria[$i]} -le ${particiones[$ct]} && ${procesoEnParticionOcupada[$i]} -eq 0 && ${sale[$i]} -eq 0 ]]; then
                        particionOcupada[$ct]=1         #La partición $j está ocupada
                        procesoEnParticionOcupada[$i]=1 #El proceso $i está en una partición ocupada
                        procesoYaHaEntrado[$i]=1        #El proceso $i ha entrado en memoria
                        ocupadas[$ct]=$i
                        entrada[$i]=$reloj
                        partConProceso[$i]=$ct
                        if [[ ${estado[$i]} != "En memoria" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                            # producido una modificación en el Estado del proceso.
                            let "poreventos=1"
                            #echo -ne "kkkk ssssssssssssssssssssss En memoria 2141\n"
                        fi
                        estado[$i]="En memoria"
                        let restante[$i]=${tiempo[$i]}
                    fi
                done
            fi
            semaforo=0

            #############################################################################################################################################################

            ###########################################################################
            #                            Px invasor
            ###########################################################################

            #############################################################################################################################################################

            #Si un proceso su tiempo restante es 0 finaliza
            if [[ ${restante[$i]} -le 0 && ${procesoEnParticionOcupada[$i]} -eq 1 && ${sale[$i]} -eq 0 ]]; then
                if [[ ${estado[$i]} != "Finalizado" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                    # producido una modificación en el Estado del proceso.
                    let "poreventos=1"
                    #echo -ne "kkkk ssssssssssssssssssssss Finalizado 2213\n"
                fi
                estado[$i]="Finalizado"
                procesoEnParticionOcupada[$i]=0 #El proceso $i está en una partición ocupada
                particionOcupada[${partConProceso[$i]}]=0
                bandera[$i]=0
                ocupadas[${partConProceso[$i]}]=0
                partConProceso[$i]=0
                sale[$i]=1
                ((hasalido++))
            fi

            #Comprobamos si hay algun Px en ejecucion, en caso contrario lanzamos el siguiente.
            semaforo=0
            for ((a = 1; a <= ${#llegada[@]}; a++)); do
                if [[ ${bandera[$a]} -eq 1 ]]; then
                    semaforo=1
                fi
            done

            tiempo_menor=1000
            x=0

            for ((x = 1; x <= ${#llegada[@]}; x++)); do

                if [[ (${estado[$x]} == "En memoria" || ${estado[$x]} == "En pausa") && ${sale[$x]} -eq 0 ]]; then

                    if [[ ${tiempo[$x]} -lt $tiempo_menor ]]; then
                        let "tiempo_menor=${tiempo[$x]}"
                        let "e = $x"

                    fi
                    #Semaforo de control de una unica expulsion (1 a 1), por cada Px
                fi
            done

            if [[ $semaforo -eq 0 ]]; then
                ####  CÓDIGO QUE ELIMINO        #  for (( h=1; h<=${#llegada[@]};h++ ))   # No hay cambio solo
                #  do
                # if [[ ${estado[$h]} == "En memoria" || ${estado[$h]} == "En pausa" ]]
                #  then
                #	if [[ ${estado[$h]} != "En ejecución" ]] 	# Sólo se cambia la variable "poreventos" si se ha
                # producido una modificación en el Estado del
                # proceso.
                #	then

                #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2244\n"
                #fi
                let "poreventos=1"
                estado[$e]="En ejecución"
                #gantt[$reloj]=$e
                inicioEjecucion[$e]=$reloj
                bandera[$e]=1
                e=$(expr ${#llegada[@]} + 1)
                # fi
                #   done
            fi

            #Salida
            if [[ $hasalido -ge ${#memoria[@]} ]]; then
                salida=s
            fi

            #Recalculo de tiempos en funcion de la espera y la respuesta de un Px
            for ((k = 1; k <= ${#tiempoEsperaProceso[@]}; k++)); do
                if [[ ${tiempoEsperaProceso[$k]} -lt 0 ]]; then
                    tiempNEsperaProceso[$k]=0
                else
                    tiempNEsperaProceso[$k]=${tiempoEsperaProceso[$k]}
                fi
            done
            for ((k = 1; k <= ${#tiempoRespuestaProceso[@]}; k++)); do
                if [[ ${tiempoRespuestaProceso[$k]} -lt 0 ]]; then
                    tiempoNRespuProceso[$k]=0
                else
                    tiempoNRespuProceso[$k]=${tiempoRespuestaProceso[$k]}
                fi
            done

        done

        ############################################################################
        # Impresion por cada ciclo de iteraciones
        ############################################################################
        ################################################################################################################################################################################################
        # Se añade el siguiente if que contiene toda la parte de impresión para ejecutarla sólo cuando
        # haya algún cambio de estado.
        ################################################################################################################################################################################################
        if [[ $poreventos -eq 0 && $optejecucion -eq 2 && $reloj -gt 0 ]]; then
            gantt[$reloj]=${gantt[$reloj - 1]}
            gantt2[$reloj]=${gantt2[$reloj - 1]} # TODO: ANTERIOR( gantt2[$reloj]==${gantt2[$reloj-1]} )
        fi

        if [[ ($poreventos -eq 1 && $optejecucion -eq 2) || $reloj -eq 0 ]]; then
            for ((i = 1; i <= ${#llegada[@]}; i++)); do

                #Llamada a la función que comprueba si ha habido cambios
                #Salidas por pantalla y salidas a informe
                if [[ $i -eq 1 ]]; then
                    echo "" >>./informeColor.txt
                    echo "" >>./informetemp.txt
                    echo -e $AMARILLO" SJF-FNI-Primer Ajuste"$NORMAL
                    echo -e " SJF-FNI-Primer Ajuste" >./informetemp.txt
                    echo $AMARILLO" SJF-FNI-Primer Ajuste"$NORMAL >./informeColor.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" | tee -a ./informetemp.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" >>./informeColor.txt
                    for ((z = 1; z <= $contadorParticiones; z++)); do
                        echo -en " ${particiones[$z]} " | tee -a ./informetemp.txt
                        echo -en " ${particiones[$z]} " >>./informeColor.txt
                    done
                    echo "" | tee -a ./informetemp.txt
                    echo "" >>./informeColor.txt
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a ./informetemp.txt
                    echo -ne $NORMAL
                    #Cabecera par informe a color
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >>./informeColor.txt
                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es mayor que 99
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi

                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                else

                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es menor o igual que 9
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                fi

            done # Fin del for

            calcularPromediosEsperaRespuesta
            representacionParticionesEnTabla

            representacionLineaTemporal

            let "poreventos=0"

        else

            for ((i = 1; i <= ${#llegada[@]}; i++)); do

                #Llamada a la función que comprueba si ha habido cambios
                #Salidas por pantalla y salidas a informe
                if [[ $i -eq 1 ]]; then
                    echo "" >>./informeColor.txt
                    echo "" >>./informetemp.txt
                    echo -e $AMARILLO" SJF-FNI-Primer Ajuste"$NORMAL
                    echo -e " SJF-FNI-Primer Ajuste" >./informetemp.txt
                    echo $AMARILLO" SJF-FNI-Primer Ajuste"$NORMAL >./informeColor.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" | tee -a ./informetemp.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" >>./informeColor.txt
                    for ((z = 1; z <= $contadorParticiones; z++)); do
                        echo -en " ${particiones[$z]} " | tee -a ./informetemp.txt
                        echo -en " ${particiones[$z]} " >>./informeColor.txt
                    done
                    echo "" | tee -a ./informetemp.txt
                    echo "" >>./informeColor.txt
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a ./informetemp.txt
                    echo -ne $NORMAL
                    #Cabecera par informe a color
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >>./informeColor.txt
                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es mayor que 99
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi

                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                else

                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es menor o igual que 9
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                fi

            done # Fin del for

            calcularPromediosEsperaRespuesta
            representacionParticionesEnTabla
            representacionLineaTemporal
            let "poreventos=0"

        fi

        # let reloj=$reloj+1 	# Esta línea estaba en la función representacionLineaTemporal pero no se
        # ejecutaba correctamente desde la función porque no se ejecutaba cuando
        # no se producía ninguna modificación del estado si no había llegado
        # ningún proceso inicialmente.
        # También dará problemas cuando no haya cambios de estado entre la
        # finalización del último proceso existente en memoria y la llegada del
        # siguiente

        ############################################################################
        #Final del if+for de Impresion por cada ciclo de iteraciones
        ############################################################################

    done #Final del 'while'
}

######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################                                                                                                  ##############
######################                                   ALGORITMO SRPT                                                 ##############
######################                                                                                                  ##############
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################

function algoritmoSRPT_AjustePrimer {
    clear

    let "poreventos=0" # Para conocer cuando se dispara el volcado. (Si vale 1 se ha disparado)
    evento1=0
    evento2=0
    evento3=0

    if [[ $reloj -eq 0 ]]; then
        evento3=1
    else
        evento3=0
    fi

    ############################################################################
    # Se ejecuta siempre
    ############################################################################

    #Comienzo del algoritmo de SRPT (ahora FCFS) con particiones distintas y ajuste mejor
    while [[ $salida != "s" ]]; do

        ############################################################################
        # Control de Particiones y Estados de los Procesos
        ############################################################################

        for ((i = 1; i <= ${#llegada[@]}; i++)); do
            #Si el proceso no ha salido, no ocupa ninguna partición y proceso anterior ha entrado ya
            if [[ "sale[$i]" -ne 1 && "procesoEnParticionOcupada[$i]" -ne 1 ]]; then
                contador=0
                if [[ ${llegada[$i]} -le $reloj ]]; then
                    #'for' para particiones
                    for ((j = 1; j <= ${#particiones[@]}; j++)); do
                        #Si el tamaño en memoria del proceso es menor que alguna partición y ésta no está ocupada...
                        if [[ ${memoria[$i]} -le ${particiones[$j]} && ${particionOcupada[$j]} -eq 0 ]]; then
                            #...metemos al proceso en esa partición

                            procesoEnParticionOcupada[$i]=1 #El proceso $i está en una partición ocupada
                            procesoYaHaEntrado[$i]=1        #El proceso $i ha entrado en memoria
                            entrada[$i]=$reloj
                            if [[ ${estado[$i]} != "En memoria" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                                # producido una modificación en el Estado del proceso.
                                let "poreventos=1"
                                #echo -ne "kkkk ssssssssssssssssssssss En memoria 2015\n"
                            fi
                            estado[$i]="En memoria"
                            let restante[$i]=${tiempo[$i]}
                            #Buscamos el primer (antes mejor) ajuste posible con la minima diff memoria sobrante
                            ##############################################################################################################################
                            ##############################################################################################################################
                            ##############################################################################################################################
                            ############################                                                                      ############################
                            ############################                        Algoritmo Primer  (ANTES MEJOR)               ############################
                            ############################                                                                      ############################
                            ##############################################################################################################################
                            ##############################################################################################################################
                            ##############################################################################################################################
                            diff_mem=100
                            diff=$j
                            for ((dm = 1; dm <= ${#particiones[@]}; dm++)); do
                                if [[ ${particionOcupada[$dm]} -eq 0 && ${particiones[$dm]} -ge ${memoria[$i]} ]]; then #si la posicion esta vacia y el tamaño de la posicion es mayor o igual a la memoria actual
                                    auxMem=$(expr ${particiones[$dm]} - ${memoria[$i]})                                 # resta entre el tamaño de la partición y el valor de la memoria correspondiente
                                fi
                                #if [[ $auxMem -lt $diff_mem && ${particionOcupada[$dm]} -eq 0 && ${particiones[$dm]} -ge ${memoria[$i]} ]]  #quitando estas lineas comentadas cambio de primer a mejor
                                #then
                                #  diff_mem=$auxMem
                                #   diff=$dm
                                #fi
                            done
                            ocupadas[$diff]=$i               # asigno a diff del array ocupadas el valor de i
                            partConProceso[$i]=$diff         # asigno el valor diff al indice i del array partConProceso
                            particionOcupada[$diff]=1        #La partición $j está ocupada    # asigno el valor 1 al indice diff del array particionOcupada
                            j=$(expr ${#particiones[@]} + 1) # asigno a j la longitud del array particiones +1
                        else
                            #...si no, si la partición estaba vacía, sigue vacía
                            if [[ ${particionOcupada[$j]} -eq 0 ]]; then
                                ((contador++))
                            fi
                        fi
                    done
                fi
            fi

            # 1) Ajustamos los estados
            if [[ ${tiempoEsperaProceso[$i]} -lt 0 && ${llegada[$i]} -ge $reloj && ${sale[$i]} -eq 0 ]]; then
                estado[$i]="Fuera del sistema"
            else
                if [[ ${procesoEnParticionOcupada[$i]} -ne 1 && ${llegada[$i]} -le $reloj && ${estado[$i]} != "Finalizado" && ${sale[$i]} -eq 0 ]]; then
                    if [[ ${estado[$i]} != "En espera" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                        # producido una modificación en el Estado del proceso.
                        let "poreventos=1"
                        #echo -ne "kkkk ssssssssssssssssssssss En espera 2060\n"
                    fi
                    estado[$i]="En espera"
                fi
            fi

            # 2)Ajustamos tiempos de respuesta segun el estado en el que nos encontramos
            if [[ ${estado[$i]} != "Finalizado" ]]; then
                let tiempoRespuestaProceso[$i]=$reloj-${llegada[$i]}
                if [[ ${tiempoRespuestaProceso[$i]} -lt 0 ]]; then
                    tiempoRespuestaProceso[$i]=0
                fi
            fi

            # 3)Si estamos en ejecución/no ejecución: ajustamos el tiempo de Espera
            if [[ ${bandera[$i]} -eq 0 && ${sale[$i]} -eq 0 ]]; then
                if [[ ${estado[$i]} != "En pausa" ]]; then
                    let tiempoEsperaProceso[$i]=${tiempoRespuestaProceso[$i]}
                else
                    let tiempoEsperaProceso[$i]=${tiempoEsperaProceso[$i]}+1
                fi
            else
                if [[ ${bandera[$i]} -eq 1 && ${sale[$i]} -eq 0 && ${bloqueo[$i]} -eq 0 ]]; then
                    let tiempoEsperaProceso[$i]=${tiempoRespuestaProceso[$i]}-$reloj+${inicioEjecucion[$i]}

                fi
            fi

            # 4)Ajustamos el tiempo restante de ejecución decrementando para el estado "En ejecución"
            if [[ ${estado[$i]} == "En ejecución" && ${sale[$i]} -eq 0 ]]; then
                let restante[$i]=${restante[$i]}-1
            fi

            #En caso de que sea el primer proceso
            if [[ $i -eq 1 && ${sale[$i]} -eq 0 && ${bloqueo[$i]} -eq 0 ]]; then

                if [[ $reloj -lt ${llegada[$i]} ]]; then
                    estado[$i]="Fuera del sistema"
                    if [[ $reloj -eq 0 ]]; then
                        evento3=1
                    else
                        evento3=0
                    fi
                else
                    if [[ ${estado[$i]} != "En ejecución" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                        # producido una modificación en el Estado del proceso.
                        let "poreventos=1"
                        #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2116\n"
                    fi
                    estado[$i]="En ejecución"
                    inicioEjecucion[$i]=$reloj
                    bandera[$i]=1
                    bloqueo[$i]=1
                    let restante[$i]=${tiempo[$i]}

                fi

            else
                for ((ct = 1; ct <= ${#particiones[@]}; ct++)); do
                    if [[ ${particionOcupada[$ct]} -eq 0 && ${llegada[$i]} -le $reloj && ${memoria[$i]} -le ${particiones[$ct]} && ${procesoEnParticionOcupada[$i]} -eq 0 && ${sale[$i]} -eq 0 ]]; then
                        particionOcupada[$ct]=1         #La partición $j está ocupada
                        procesoEnParticionOcupada[$i]=1 #El proceso $i está en una partición ocupada
                        procesoYaHaEntrado[$i]=1        #El proceso $i ha entrado en memoria
                        ocupadas[$ct]=$i
                        entrada[$i]=$reloj
                        partConProceso[$i]=$ct
                        if [[ ${estado[$i]} != "En memoria" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                            # producido una modificación en el Estado del proceso.
                            let "poreventos=1"
                            #echo -ne "kkkk ssssssssssssssssssssss En memoria 2141\n"
                        fi
                        estado[$i]="En memoria"
                        let restante[$i]=${tiempo[$i]}+1
                    fi
                done
            fi

            semaforo=0

            ##############################################################################################################################
            ##############################################################################################################################
            ##############################################################################################################################
            ############################                                                                      ############################
            ############################    SRPT Expropiacion ante un Px que tiene menor tiempo de            ############################
            ############################      ejecución que el que esta ejecutandose                          ############################
            ############################                                                                      ############################
            ##############################################################################################################################
            ##############################################################################################################################
            ##############################################################################################################################

            ##############################################################################################################################
            ##############################################################################################################################
            ##############################################################################################################################
            ############################                                                                      ############################
            ############################                                                                      ############################
            ############################                         Algoritmo SRPT                               ############################
            ############################                                                                      ############################
            ############################                                                                      ############################
            ##############################################################################################################################
            ##############################################################################################################################
            ##############################################################################################################################

            ###################################################################################################################################################################
            ###################################################################################################################################################################
            f=0
            for ((e = 1; e <= ${#llegada[@]}; e++)); do
                for ((ex = 1; ex <= ${#llegada[@]}; ex++)); do
                    if [[ ${bandera[$ex]} -eq 1 ]]; then
                        if [[ ${restante[$ex]} -lt ${restante[$e]} ]]; then
                            abortar=1
                        fi
                    fi
                done
                if [[ ${estado[$e]} == "En memoria" || ${estado[$e]} == "En pausa" && $semaforo -eq 0 && ${sale[$e]} -eq 0 ]]; then #&& $abortar -eq 0
                    #Semaforo de control de una unica expulsion (1 a 1), por cada Px
                    expulsar=0

                    tiempo_menor=1000
                    x=0
                    f=0
                    for ((x = 1; x <= ${#llegada[@]}; x++)); do

                        if [[ (${estado[$x]} == "En memoria" || ${estado[$x]} == "En pausa") && ${sale[$x]} -eq 0 ]]; then

                            if [[ ${restante[$x]} -lt $tiempo_menor ]]; then
                                let "tiempo_menor=${restante[$x]}"
                                let "f = $x"

                            fi
                            #Semaforo de control de una unica expulsion (1 a 1), por cada Px
                        fi
                    done

                    for ((m = 1; m <= ${#particiones[@]}; m++)); do
                        if [[ $expulsar -eq 0 && ${restante[${ocupadas[$m]}]} -gt ${restante[$f]} && ${estado[${ocupadas[$m]}]} == "En ejecución" ]]; then
                            expulsar=1

                            if [[ ${estado[$m]} != "En pausa" ]]; then
                                let "poreventos=1"
                            fi
                            estado[${ocupadas[$m]}]="En pausa"
                            bandera[${ocupadas[$m]}]=0
                            inicioEjecucion[$f]=$reloj

                            if [[ ${estado[$f]} != "En ejecución" ]]; then
                                let "poreventos=1"
                            fi
                            estado[$f]="En ejecución"
                            bandera[$f]=1
                        fi
                    done
                fi
            done

            ###################################################################################################################################################################
            ###################################################################################################################################################################
            ###################################################################################################################################################################

            #Si un proceso su tiempo restante es 0 finaliza
            if [[ ${restante[$i]} -le 0 && ${procesoEnParticionOcupada[$i]} -eq 1 && ${sale[$i]} -eq 0 ]]; then
                if [[ ${estado[$i]} != "Finalizado" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                    # producido una modificación en el Estado del proceso.
                    let "poreventos=1"
                    #echo -ne "kkkk ssssssssssssssssssssss Finalizado 2213\n"
                fi
                estado[$i]="Finalizado"
                procesoEnParticionOcupada[$i]=0 #El proceso $i está en una partición ocupada
                particionOcupada[${partConProceso[$i]}]=0
                bandera[$i]=0
                ocupadas[${partConProceso[$i]}]=0
                partConProceso[$i]=0
                sale[$i]=1
                ((hasalido++))
            fi

            #Comprobamos si hay algun Px en ejecucion, en caso contrario lanzamos el siguiente.
            semaforo=0
            for ((a = 1; a <= ${#llegada[@]}; a++)); do
                if [[ ${bandera[$a]} -eq 1 ]]; then
                    semaforo=1
                fi
            done
            tiempo_menor2=1000
            x2=0
            f2=0
            for ((x2 = 1; x2 <= ${#llegada[@]}; x2++)); do

                if [[ (${estado[$x2]} == "En memoria" || ${estado[$x2]} == "En pausa") && ${sale[$x2]} -eq 0 ]]; then

                    if [[ ${restante[$x2]} -lt $tiempo_menor2 ]]; then
                        let "tiempo_menor2=${restante[$x2]}"
                        let "f2 = $x2"

                    fi
                    #Semaforo de control de una unica expulsion (1 a 1), por cada Px
                fi
            done
            if [[ $semaforo -eq 0 ]]; then
                #for (( h=1; h<=${#llegada[@]};h++ ))
                #do
                #   if [[ ${estado[$h]} == "En memoria" || ${estado[$h]} == "En pausa" ]]
                #     then
                #		if [[ ${estado[$h]} != "En ejecución" ]] 	# Sólo se cambia la variable "poreventos" si se ha
                # producido una modificación en el Estado del
                # proceso.
                #	then
                let "poreventos=1"
                #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2244\n"
                #fi
                estado[$f2]="En ejecución"
                inicioEjecucion[$f2]=$reloj
                bandera[$f2]=1
                #h=`expr ${#llegada[@]} + 1`
                # fi
                #done
            fi

            #Salida
            if [[ $hasalido -ge ${#memoria[@]} ]]; then
                salida=s
            fi

            #Recalculo de tiempos en funcion de la espera y la respuesta de un Px
            for ((k = 1; k <= ${#tiempoEsperaProceso[@]}; k++)); do
                if [[ ${tiempoEsperaProceso[$k]} -lt 0 ]]; then
                    tiempNEsperaProceso[$k]=0
                else
                    tiempNEsperaProceso[$k]=${tiempoEsperaProceso[$k]}
                fi
            done
            for ((k = 1; k <= ${#tiempoRespuestaProceso[@]}; k++)); do
                if [[ ${tiempoRespuestaProceso[$k]} -lt 0 ]]; then
                    tiempoNRespuProceso[$k]=0
                else
                    tiempoNRespuProceso[$k]=${tiempoRespuestaProceso[$k]}
                fi
            done

        done

        ############################################################################
        # Impresion por cada ciclo de iteraciones
        ############################################################################
        ################################################################################################################################################################################################
        # Se añade el siguiente if que contiene toda la parte de impresión para ejecutarla sólo cuando
        # haya algún cambio de estado.
        ################################################################################################################################################################################################
        if [[ $poreventos -eq 0 && $optejecucion -eq 2 && $reloj -gt 0 ]]; then
            gantt[$reloj]=${gantt[$reloj - 1]}
            gantt2[$reloj]=${gantt2[$reloj - 1]} # TODO: ANTERIOR( gantt2[$reloj]==${gantt2[$reloj-1]} )
        fi
        if [[ (($poreventos -eq 1) && ($optejecucion -eq 2)) || $reloj -eq 0 ]]; then
            for ((i = 1; i <= ${#llegada[@]}; i++)); do

                #Llamada a la función que comprueba si ha habido cambios
                #Salidas por pantalla y salidas a informe
                if [[ $i -eq 1 ]]; then
                    echo "" >>./informeColor.txt
                    echo "" >>./informetemp.txt
                    echo -e $AMARILLO" SRPT-FNI-Primer Ajuste"$NORMAL
                    echo -e " SRPT-FNI-Primer Ajuste" >./informetemp.txt
                    echo $AMARILLO" SRPT-FNI-Primer Ajuste"$NORMAL >./informeColor.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" | tee -a ./informetemp.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" >>./informeColor.txt
                    for ((z = 1; z <= $contadorParticiones; z++)); do
                        echo -en " ${particiones[$z]} " | tee -a ./informetemp.txt
                        echo -en " ${particiones[$z]} " >>./informeColor.txt
                    done
                    echo "" | tee -a ./informetemp.txt
                    echo "" >>./informeColor.txt
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a ./informetemp.txt
                    echo -ne $NORMAL
                    #Cabecera par informe a color
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >>./informeColor.txt
                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es mayor que 99
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi

                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                else

                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es menor o igual que 9
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                fi

            done # Fin del for

            calcularPromediosEsperaRespuesta
            representacionParticionesEnTabla
            representacionLineaTemporal
            let "poreventos=0"
        elif [[ $optejecucion -ne 2 ]]; then
            for ((i = 1; i <= ${#llegada[@]}; i++)); do

                #Llamada a la función que comprueba si ha habido cambios
                #Salidas por pantalla y salidas a informe
                if [[ $i -eq 1 ]]; then
                    echo "" >>./informeColor.txt
                    echo "" >>./informetemp.txt
                    echo -e $AMARILLO" SRPT-FNI-Primer Ajuste"$NORMAL
                    echo -e " SRPT-FNI-Primer Ajuste" >./informetemp.txt
                    echo $AMARILLO" SRPT-FNI-Primer Ajuste"$NORMAL >./informeColor.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" | tee -a ./informetemp.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" >>./informeColor.txt
                    for ((z = 1; z <= $contadorParticiones; z++)); do
                        echo -en " ${particiones[$z]} " | tee -a ./informetemp.txt
                        echo -en " ${particiones[$z]} " >>./informeColor.txt
                    done
                    echo "" | tee -a ./informetemp.txt
                    echo "" >>./informeColor.txt
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a ./informetemp.txt
                    echo -ne $NORMAL
                    #Cabecera par informe a color
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >>./informeColor.txt
                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es mayor que 99
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi

                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                else

                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es menor o igual que 9
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                fi

            done # Fin del for

            calcularPromediosEsperaRespuesta
            representacionParticionesEnTabla
            representacionLineaTemporal
            let "poreventos=0"
        fi
        let reloj=$reloj+1 # Esta línea estaba en la función representacionLineaTemporal pero no se
                           # ejecutaba correctamente desde la función porque no se ejecutaba cuando
                           # no se producía ninguna modificación del estado si no había llegado
                           # ningún proceso inicialmente.
                           # También dará problemas cuando no haya cambios de estado entre la
                           # finalización del último proceso existente en memoria y la llegada del
                           # siguiente

        ############################################################################
        # Final del if+for de Impresion por cada ciclo de iteraciones
        ############################################################################

    done #Final del 'while'
}

######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
###################################                                                                ###################################
###################################         Función con Algoritmo FCFS-FNI-Primer                  ###################################
###################################             Que antes era SRPT-FNI-Mejor                       ###################################
###################################                                                                ###################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################
#     Sinopsis:   función que establece los estados de cada proceso según el estado de las particiones.             ##################
#       Además, asigna los tiempos adecuados por proceso y permite mostrar una salida a pantalla/informe            ##################
######################################################################################################################################
######################################################################################################################################
######################################################################################################################################

function algoritmoFCFS_AjustePrimer {
    clear

    let "poreventos=0" # Para conocer cuando se dispara el volcado. (Si vale 1 se ha disparado)
    evento1=0
    evento2=0
    evento3=0

    if [[ $reloj -eq 0 ]]; then
        evento3=1
    else
        evento3=0
    fi

    ############################################################################
    # Se ejecuta siempre
    ############################################################################

    #Comienzo del algoritmo de SRPT (ahora FCFS) con particiones distintas y ajuste mejor
    while [[ $salida != "s" ]]; do

        ############################################################################
        # Control de Particiones y Estados de los Procesos
        ############################################################################

        for ((i = 1; i <= ${#llegada[@]}; i++)); do
            #Si el proceso no ha salido, no ocupa ninguna partición y proceso anterior ha entrado ya
            if [[ "sale[$i]" -ne 1 && "procesoEnParticionOcupada[$i]" -ne 1 ]]; then
                contador=0
                if [[ ${llegada[$i]} -le $reloj ]]; then
                    #'for' para particiones
                    for ((j = 1; j <= ${#particiones[@]}; j++)); do
                        #Si el tamaño en memoria del proceso es menor que alguna partición y ésta no está ocupada...
                        if [[ ${memoria[$i]} -le ${particiones[$j]} && ${particionOcupada[$j]} -eq 0 ]]; then
                            #...metemos al proceso en esa partición

                            procesoEnParticionOcupada[$i]=1 #El proceso $i está en una partición ocupada
                            procesoYaHaEntrado[$i]=1        #El proceso $i ha entrado en memoria
                            entrada[$i]=$reloj
                            if [[ ${estado[$i]} != "En memoria" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                                # producido una modificación en el Estado del proceso.
                                let "poreventos=1"
                                #echo -ne "kkkk ssssssssssssssssssssss En memoria 2015\n"
                            fi
                            estado[$i]="En memoria"
                            let restante[$i]=${tiempo[$i]}
                            #Buscamos el primer (antes mejor) ajuste posible con la minima diff memoria sobrante
                            ##############################################################################################################################
                            ##############################################################################################################################
                            ##############################################################################################################################
                            ############################                                                                      ############################
                            ############################                        Algoritmo Primer  (ANTES MEJOR)               ############################
                            ############################                                                                      ############################
                            ##############################################################################################################################
                            ##############################################################################################################################
                            ##############################################################################################################################
                            diff_mem=100
                            diff=$j
                            for ((dm = 1; dm <= ${#particiones[@]}; dm++)); do
                                if [[ ${particionOcupada[$dm]} -eq 0 && ${particiones[$dm]} -ge ${memoria[$i]} ]]; then #si la posicion esta vacia y el tamaño de la posicion es mayor o igual a la memoria actual
                                    auxMem=$(expr ${particiones[$dm]} - ${memoria[$i]})                                 # resta entre el tamaño de la partición y el valor de la memoria correspondiente
                                fi
                                #if [[ $auxMem -lt $diff_mem && ${particionOcupada[$dm]} -eq 0 && ${particiones[$dm]} -ge ${memoria[$i]} ]]  #quitando estas lineas comentadas cambio de primer a mejor
                                #then
                                #  diff_mem=$auxMem
                                #   diff=$dm
                                #fi
                            done
                            ocupadas[$diff]=$i               # asigno a diff del array ocupadas el valor de i
                            partConProceso[$i]=$diff         # asigno el valor diff al indice i del array partConProceso
                            particionOcupada[$diff]=1        #La partición $j está ocupada    # asigno el valor 1 al indice diff del array particionOcupada
                            j=$(expr ${#particiones[@]} + 1) # asigno a j la longitud del array particiones +1
                        else
                            #...si no, si la partición estaba vacía, sigue vacía
                            if [[ ${particionOcupada[$j]} -eq 0 ]]; then
                                ((contador++))
                            fi
                        fi
                    done
                fi
            fi

            # 1) Ajustamos los estados
            if [[ ${tiempoEsperaProceso[$i]} -lt 0 && ${llegada[$i]} -ge $reloj && ${sale[$i]} -eq 0 ]]; then
                estado[$i]="Fuera del sistema"
            else
                if [[ ${procesoEnParticionOcupada[$i]} -ne 1 && ${llegada[$i]} -le $reloj && ${estado[$i]} != "Finalizado" && ${sale[$i]} -eq 0 ]]; then
                    if [[ ${estado[$i]} != "En espera" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                        # producido una modificación en el Estado del proceso.
                        let "poreventos=1"
                        #echo -ne "kkkk ssssssssssssssssssssss En espera 2060\n"
                    fi
                    estado[$i]="En espera"
                fi
            fi

            # 2)Ajustamos tiempos de respuesta segun el estado en el que nos encontramos
            if [[ ${estado[$i]} != "Finalizado" ]]; then
                let tiempoRespuestaProceso[$i]=$reloj-${llegada[$i]}
                if [[ ${tiempoRespuestaProceso[$i]} -lt 0 ]]; then
                    tiempoRespuestaProceso[$i]=0
                fi
            fi

            # 3)Si estamos en ejecución/no ejecución: ajustamos el tiempo de Espera
            if [[ ${bandera[$i]} -eq 0 && ${sale[$i]} -eq 0 ]]; then
                if [[ ${estado[$i]} != "En pausa" ]]; then
                    let tiempoEsperaProceso[$i]=${tiempoRespuestaProceso[$i]}
                else
                    let tiempoEsperaProceso[$i]=${tiempoEsperaProceso[$i]}+1
                fi
            else
                if [[ ${bandera[$i]} -eq 1 && ${sale[$i]} -eq 0 && ${bloqueo[$i]} -eq 0 ]]; then
                    let tiempoEsperaProceso[$i]=${tiempoRespuestaProceso[$i]}-$reloj+${inicioEjecucion[$i]}

                fi
            fi

            # 4)Ajustamos el tiempo restante de ejecución decrementando para el estado "En ejecución"
            if [[ ${estado[$i]} == "En ejecución" && ${sale[$i]} -eq 0 ]]; then
                let restante[$i]=${restante[$i]}-1
            fi

            #En caso de que sea el primer proceso
            if [[ $i -eq 1 && ${sale[$i]} -eq 0 && ${bloqueo[$i]} -eq 0 ]]; then

                if [[ $reloj -lt ${llegada[$i]} ]]; then
                    estado[$i]="Fuera del sistema"
                    if [[ $reloj -eq 0 ]]; then
                        evento3=1
                    else
                        evento3=0
                    fi
                else
                    if [[ ${estado[$i]} != "En ejecución" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                        # producido una modificación en el Estado del proceso.
                        let "poreventos=1"
                        #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2116\n"
                    fi
                    estado[$i]="En ejecución"
                    inicioEjecucion[$i]=$reloj
                    bandera[$i]=1
                    bloqueo[$i]=1
                    let restante[$i]=${tiempo[$i]}

                fi

            else
                for ((ct = 1; ct <= ${#particiones[@]}; ct++)); do
                    if [[ ${particionOcupada[$ct]} -eq 0 && ${llegada[$i]} -le $reloj && ${memoria[$i]} -le ${particiones[$ct]} && ${procesoEnParticionOcupada[$i]} -eq 0 && ${sale[$i]} -eq 0 ]]; then
                        particionOcupada[$ct]=1         #La partición $j está ocupada
                        procesoEnParticionOcupada[$i]=1 #El proceso $i está en una partición ocupada
                        procesoYaHaEntrado[$i]=1        #El proceso $i ha entrado en memoria
                        ocupadas[$ct]=$i
                        entrada[$i]=$reloj
                        partConProceso[$i]=$ct
                        if [[ ${estado[$i]} != "En memoria" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                            # producido una modificación en el Estado del proceso.
                            let "poreventos=1"
                            #echo -ne "kkkk ssssssssssssssssssssss En memoria 2141\n"
                        fi
                        estado[$i]="En memoria"
                        let restante[$i]=${tiempo[$i]}+1
                    fi
                done
            fi

            semaforo=0

            ##############################################################################################################################
            ##############################################################################################################################
            ##############################################################################################################################
            ############################                                                                      ############################
            ############################                                                                      ############################
            ############################                         Algoritmo FCFS                               ############################
            ############################                                                                      ############################
            ############################                                                                      ############################
            ##############################################################################################################################
            ##############################################################################################################################
            ##############################################################################################################################

            ###################################################################################################################################################################
            ###################################################################################################################################################################
            ###################################################################################################################################################################

            #for ((e=1; e<=${#llegada[@]}; e++))
            #do
            #for ((ex=1; ex<=${#llegada[@]}; ex++ ))
            #do
            #if [[ ${bandera[$ex]} -eq 1 ]]
            #then
            #if [[ ${restante[$ex]} -lt ${restante[$e]} ]]
            #then
            #abortar=1
            #fi
            #fi

            #done
            #if [[ ${estado[$e]} == "En memoria" || ${estado[$e]} == "En pausa" && $semaforo -eq 0 && ${sale[$e]} -eq 0  ]] #&& $abortar -eq 0
            #then
            #Semaforo de control de una unica expulsion (1 a 1), por cada Px
            #expulsar=0
            #for ((m=1; m<=${#particiones[@]}; m++))
            #do

            #if [[ $expulsar -eq 0 && ${restante[${ocupadas[$m]}]} -gt ${restante[$e]} && ${estado[${ocupadas[$m]}]} == "En ejecución" ]]
            #then

            #Px expulsado

            #expulsar=1
            #if [[ ${estado[$m]} != "En pausa" ]]
            #then
            #let "poreventos=1" 	# Sólo se cambia la variable "poreventos" si se ha
            # producido una modificación en el Estado del proceso.
            #echo -ne "kkkk ssssssssssssssssssssss En pausa 2182\n"
            #fi
            #estado[${ocupadas[$m]}]="En pausa"
            #bandera[${ocupadas[$m]}]=0

            ############################################################################
            #Px invasor
            ############################################################################

            #inicioEjecucion[$e]=$reloj
            #if [[ ${estado[$e]} != "En ejecución" ]] 	# Sólo se cambia la variable "poreventos" si se ha
            # producido una modificación en el Estado del
            # proceso.
            #then
            #let "poreventos=1"
            # No quitar #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2192\n"
            #fi
            #estado[$e]="En ejecución"
            #bandera[$e]=1
            #fi
            #done

            #fi
            #done
            ###################################################################################################################################################################
            ###################################################################################################################################################################
            ###################################################################################################################################################################

            #Si un proceso su tiempo restante es 0 finaliza
            if [[ ${restante[$i]} -le 0 && ${procesoEnParticionOcupada[$i]} -eq 1 && ${sale[$i]} -eq 0 ]]; then
                if [[ ${estado[$i]} != "Finalizado" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                    # producido una modificación en el Estado del proceso.
                    let "poreventos=1"
                    #echo -ne "kkkk ssssssssssssssssssssss Finalizado 2213\n"
                fi
                estado[$i]="Finalizado"
                procesoEnParticionOcupada[$i]=0 #El proceso $i está en una partición ocupada
                particionOcupada[${partConProceso[$i]}]=0
                bandera[$i]=0
                ocupadas[${partConProceso[$i]}]=0
                partConProceso[$i]=0
                sale[$i]=1
                ((hasalido++))
            fi

            #Comprobamos si hay algun Px en ejecucion, en caso contrario lanzamos el siguiente.
            semaforo=0
            for ((a = 1; a <= ${#llegada[@]}; a++)); do
                if [[ ${bandera[$a]} -eq 1 ]]; then
                    semaforo=1
                fi
            done

            if [[ $semaforo -eq 0 ]]; then
                for ((h = 1; h <= ${#llegada[@]}; h++)); do
                    if [[ ${estado[$h]} == "En memoria" || ${estado[$h]} == "En pausa" ]]; then
                        if [[ ${estado[$h]} != "En ejecución" ]]; then # Sólo se cambia la variable "poreventos" si se ha
                            # producido una modificación en el Estado del
                            # proceso.
                            let "poreventos=1"
                            #echo -ne "kkkk ssssssssssssssssssssss En ejecución 2244\n"
                        fi
                        estado[$h]="En ejecución"
                        inicioEjecucion[$h]=$reloj
                        bandera[$h]=1
                        h=$(expr ${#llegada[@]} + 1)
                    fi
                done
            fi

            #Salida
            if [[ $hasalido -ge ${#memoria[@]} ]]; then
                salida=s
            fi

            #Recalculo de tiempos en funcion de la espera y la respuesta de un Px
            for ((k = 1; k <= ${#tiempoEsperaProceso[@]}; k++)); do
                if [[ ${tiempoEsperaProceso[$k]} -lt 0 ]]; then
                    tiempNEsperaProceso[$k]=0
                else
                    tiempNEsperaProceso[$k]=${tiempoEsperaProceso[$k]}
                fi
            done
            for ((k = 1; k <= ${#tiempoRespuestaProceso[@]}; k++)); do
                if [[ ${tiempoRespuestaProceso[$k]} -lt 0 ]]; then
                    tiempoNRespuProceso[$k]=0
                else
                    tiempoNRespuProceso[$k]=${tiempoRespuestaProceso[$k]}
                fi
            done

        done

        ############################################################################
        # Impresion por cada ciclo de iteraciones
        ############################################################################
        ################################################################################################################################################################################################
        # Se añade el siguiente if que contiene toda la parte de impresión para ejecutarla sólo cuando
        # haya algún cambio de estado.
        ################################################################################################################################################################################################
        if [[ $poreventos -eq 0 && $optejecucion -eq 2 && $reloj -gt 0 ]]; then
            gantt[$reloj]=${gantt[$reloj - 1]}
            gantt2[$reloj]=${gantt2[$reloj - 1]} # TODO: ANTERIOR( gantt2[$reloj]==${gantt2[$reloj-1]} )
        fi
        if [[ (($poreventos -eq 1) && ($optejecucion -eq 2)) || $reloj -eq 0 ]]; then
            for ((i = 1; i <= ${#llegada[@]}; i++)); do

                #Llamada a la función que comprueba si ha habido cambios
                #Salidas por pantalla y salidas a informe
                if [[ $i -eq 1 ]]; then
                    echo "" >>./informeColor.txt
                    echo "" >>./informetemp.txt
                    echo -e $AMARILLO" FCFS-FNI-Primer Ajuste"$NORMAL
                    echo -e " FCFS-FNI-Primer Ajuste" >./informetemp.txt
                    echo $AMARILLO" FCFS-FNI-Primer Ajuste"$NORMAL >./informeColor.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" | tee -a ./informetemp.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" >>./informeColor.txt
                    for ((z = 1; z <= $contadorParticiones; z++)); do
                        echo -en " ${particiones[$z]} " | tee -a ./informetemp.txt
                        echo -en " ${particiones[$z]} " >>./informeColor.txt
                    done
                    echo "" | tee -a ./informetemp.txt
                    echo "" >>./informeColor.txt
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a ./informetemp.txt
                    echo -ne $NORMAL
                    #Cabecera par informe a color
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >>./informeColor.txt
                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es mayor que 99
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi

                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                else

                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es menor o igual que 9
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                fi

            done # Fin del for

            calcularPromediosEsperaRespuesta
            representacionParticionesEnTabla
            representacionLineaTemporal
            let "poreventos=0"
        elif [[ $optejecucion -ne 2 ]]; then
            for ((i = 1; i <= ${#llegada[@]}; i++)); do

                #Llamada a la función que comprueba si ha habido cambios
                #Salidas por pantalla y salidas a informe
                if [[ $i -eq 1 ]]; then
                    echo "" >>./informeColor.txt
                    echo "" >>./informetemp.txt
                    echo -e $AMARILLO" FCFS-FNI-Primer Ajuste"$NORMAL
                    echo -e " FCFS-FNI-Primer Ajuste" >./informetemp.txt
                    echo $AMARILLO" FCFS-FNI-Primer Ajuste"$NORMAL >./informeColor.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" | tee -a ./informetemp.txt
                    echo -ne " T: $reloj\tTamaño de las particiones:" >>./informeColor.txt
                    for ((z = 1; z <= $contadorParticiones; z++)); do
                        echo -en " ${particiones[$z]} " | tee -a ./informetemp.txt
                        echo -en " ${particiones[$z]} " >>./informeColor.txt
                    done
                    echo "" | tee -a ./informetemp.txt
                    echo "" >>./informeColor.txt
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a ./informetemp.txt
                    echo -ne $NORMAL
                    #Cabecera par informe a color
                    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >>./informeColor.txt
                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es mayor que 99
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi

                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                else

                    restante[$i]=$((${tiempo[$i]} + ${tiempNEsperaProceso[$i]} - ${tiempoNRespuProceso[$i]}))
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}"
                    echo -ne " ${proceso[$i]}" >>./informetemp.txt
                    echo -ne " ${colores[$i % 6]}${proceso[$i]}" >>./informeColor.txt
                    if [[ ${llegada[$i]} -gt 99 ]]; then #Si es menor o igual que 9
                        echo -ne " ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${llegada[$i]}" >>./informetemp.txt
                    elif [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${llegada[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${llegada[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempo[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${tiempo[$i]}" >>./informetemp.txt
                    elif [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempo[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempo[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${memoria[$i]} -gt 99 ]]; then
                        echo -ne " ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne " ${memoria[$i]}" >>./informetemp.txt
                    elif [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${memoria[$i]}" >>./informetemp.txt
                    else
                        echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${memoria[$i]}" >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}-" | tee -a ./informeColor.txt
                        echo -ne "    -" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "  ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "    ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi
                    if [[ ${tiempNEsperaProceso[$i]} -le 99 && ${tiempNEsperaProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a ./informeColor.txt
                        echo -ne "   ${tiempNEsperaProceso[$i]}" >>./informetemp.txt
                    fi

                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "    ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "    - " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "    ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${tiempoNRespuProceso[$i]} -le 99 && ${tiempoNRespuProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${tiempoNRespuProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ "${estado[$i]}" == "Fuera del sistema" ]]; then
                        echo -ne "   ${colores[$i % 6]}- " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne " ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then #Si es menor o igual que 9
                        echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${restante[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${restante[$i]} -le 99 && ${restante[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" ]]; then
                        echo -ne "  ${colores[$i % 6]}${restante[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${restante[$i]} " >>./informetemp.txt
                    fi

                    if [[ ("${estado[$i]}" == "Fuera del sistema" || "${estado[$i]}" == "Finalizado" || "${estado[$i]}" == "En espera") ]]; then
                        echo -ne "   - " | tee -a ./informeColor.txt
                        echo -ne "   - " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -gt 99 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne " ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne " ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "   ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "   ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    if [[ ${partConProceso[$i]} -le 99 && ${partConProceso[$i]} -gt 9 && "${estado[$i]}" != "Fuera del sistema" && "${estado[$i]}" != "Finalizado" && "${estado[$i]}" != "En espera" ]]; then
                        echo -ne "  ${partConProceso[$i]} " | tee -a ./informeColor.txt
                        echo -ne "  ${partConProceso[$i]} " >>./informetemp.txt
                    fi
                    echo -ne "${estado[$i]} " | tee -a ./informeColor.txt
                    echo -ne "${estado[$i]} " >>./informetemp.txt
                    echo "" | tee -a ./informeColor.txt
                    echo "" >>./informetemp.txt

                fi

            done # Fin del for

            calcularPromediosEsperaRespuesta
            representacionParticionesEnTabla
            representacionLineaTemporal
            let "poreventos=0"
        fi
        let reloj=$reloj+1 # Esta línea estaba en la función representacionLineaTemporal pero no se
                           # ejecutaba correctamente desde la función porque no se ejecutaba cuando
                           # no se producía ninguna modificación del estado si no había llegado
                           # ningún proceso inicialmente.
                           # También dará problemas cuando no haya cambios de estado entre la
                           # finalización del último proceso existente en memoria y la llegada del
                           # siguiente

        ############################################################################
        #Final del if+for de Impresion por cada ciclo de iteraciones
        ############################################################################

    done #Final del 'while'
}

################################################################################################################################################################################################
# Sinopsis:   función muestra, en pantalla/informe, el estado de cada partición según el instante de tiempo
################################################################################################################################################################################################

function representacionParticionesEnTabla {
    
    #Creo una variable global con el valor de la suma de los tiempos de ejecucion y llegada para saber el numero de espacios que debo dejar delante de 
    #los números

    # Declaro una variable para almacenar la suma
    sumaParaEspacios=0

    for ((i = 1; i <= ${#proceso[@]}; i++)); do
	# Sumar los valores de tiempo de llegada y ejecución
	sumaParaEspacios=$((sumaParaEspacios + ${llegada[$i]} + ${tiempo[$i]}))
    done
    local maxCaracteres=0

	# Asignar un valor a maxCaracteres según la cantidad de dígitos en sumaParaEspacios
	if ((sumaParaEspacios >= 1 && sumaParaEspacios <= 99)); then
	    maxCaracteres=3
	elif ((sumaParaEspacios >= 100 && sumaParaEspacios <= 999)); then
	    maxCaracteres=4
	elif ((sumaParaEspacios >= 1000 && sumaParaEspacios <= 9999)); then
	    maxCaracteres=5
	elif ((sumaParaEspacios >= 10000 && sumaParaEspacios <= 99999)); then
	    maxCaracteres=6
	elif ((sumaParaEspacios >= 100000 && sumaParaEspacios <= 999999)); then
	    maxCaracteres=7
    	elif ((sumaParaEspacios >= 1000000 && sumaParaEspacios <= 999999)); then
	    maxCaracteres=8
    	elif ((sumaParaEspacios >= 10000000 && sumaParaEspacios <= 9999999)); then
	    maxCaracteres=9
	elif ((sumaParaEspacios >= 100000000 && sumaParaEspacios <= 99999999)); then
	    maxCaracteres=10
    	fi

    local terminal=`tput cols`
    
    echo ""


    # GENERACIÓN STRING DE PROCESOS
    local bandaProcesos=("    |")
    local bandaProcesosColor=("    |")
    local n=0 # Línea de la banda
    local numCaracteres=5

    for ((i = 1; i <= ${#particiones[@]}; i++)); do
        local x=0 # Variable que indica si se ha añadido un proceso a la banda

        for ((j = 1; j <= ${#partConProceso[@]}; j++)); do
            if [[ $i -eq ${partConProceso[$j]} && (${estado[$j]} = "En memoria" || ${estado[$j]} = "En ejecución" || ${estado[$j]} = "En pausa") ]]; then # El proceso se puede imprimir en memoria
                if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                    n=$(($n + 1)) # Se pasa a la siguiente línea
                    bandaProcesos[n]="     "
                    bandaProcesosColor[n]="     "
                    numCaracteres=5
                fi
                # Se añade el proceso a la banda
                bandaProcesos[n]+=`printf "%-${maxCaracteres}s" ${proceso[$j]}`
                bandaProcesosColor[n]+=`printf "${colores[$j % 6]}%-${maxCaracteres}s\033[0m" ${proceso[$j]}`
                numCaracteres=$(($numCaracteres + $maxCaracteres))
                # Se añade los espacios correspondientes al proceso
                for ((k = 0; k < $((${particiones[$i]} - 1)); k++)); do
                    if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                        n=$(($n + 1)) # Se pasa a la siguiente línea
                        bandaProcesos[n]="     "
                        bandaProcesosColor[n]="     "
                        numCaracteres=5
                    fi
                    bandaProcesos[n]+=`printf "%$(($maxCaracteres))s" ""`
                    bandaProcesosColor[n]+=`printf "%$(($maxCaracteres))s" ""`
                    numCaracteres=$(($numCaracteres + $maxCaracteres))
                done
                x=1
                break
            fi
        done
        if [[ $x -eq 0 ]]; then # No se ha añadido ningún proceso a la banda
            for ((k = 0; k < ${particiones[$i]}; k++)); do
                if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                    n=$(($n + 1)) # Se pasa a la siguiente línea
                    bandaProcesos[n]="     "
                    bandaProcesosColor[n]="     "
                    numCaracteres=5
                fi
                bandaProcesos[n]+=`printf "%$(($maxCaracteres))s" ""`
                bandaProcesosColor[n]+=`printf "%$(($maxCaracteres))s" ""`
                numCaracteres=$(($numCaracteres + $maxCaracteres))
            done
        fi

        # AÑADIR SEPARADOR DE PARTICIONES
        if [[ $i -lt ${#particiones[@]} ]]; then
            if [[ $(($numCaracteres + 1 + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaProcesos[n]="     "
                bandaProcesosColor[n]="     "
                numCaracteres=5
            fi
            bandaProcesos[n]+=" "
            bandaProcesosColor[n]+=" "
            numCaracteres=$(($numCaracteres + 1))
        fi
    done
    # Añadir final de banda
    if [[ $(($numCaracteres + 5 + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
        n=$(($n + 1)) # Se pasa a la siguiente línea
        bandaProcesos[n]="     "
        bandaProcesosColor[n]="     "
        numCaracteres=5
    fi
    bandaProcesos[n]+=`printf "|    %$(($maxCaracteres))s" ""`
    bandaProcesosColor[n]+=`printf "|    %$(($maxCaracteres))s" ""`


    # GENERACIÓN STRING DE MEMORIA
    local bandaMemoria=(" BM |")
    local bandaMemoriaColor=(" BM |")
    local n=0 # Línea de la banda
    local numCaracteres=5

    for ((i = 1; i <= ${#particiones[@]}; i++)); do
        local x=0 # Variable que indica si se ha añadido un proceso a la banda

        for ((j = 1; j <= ${#partConProceso[@]}; j++)); do
            if [[ $i -eq ${partConProceso[$j]} && (${estado[$j]} = "En memoria" || ${estado[$j]} = "En ejecución" || ${estado[$j]} = "En pausa") ]]; then # El proceso se puede imprimir en memoria
                for (( k = 0; k < ${particiones[$i]}; k++ )); do
                    if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                        n=$(($n + 1)) # Se pasa a la siguiente línea
                        bandaMemoria[n]="     "
                        bandaMemoriaColor[n]="     "
                        numCaracteres=5
                    fi

                    for (( l = 0; l < $maxCaracteres; l++ )); do
                        if [[ $k -lt ${memoria[$j]} ]]; then
                            bandaMemoria[n]+="█"
                            bandaMemoriaColor[n]+=${colores[$j % 6]}"█\033[0m"
                        else
                            bandaMemoria[n]+="-"
                            bandaMemoriaColor[n]+=$NORMAL"█\033[0m"
                        fi
                    done
                    numCaracteres=$(($numCaracteres + $maxCaracteres))
                done                    
                x=1
                break
            fi
        done
        if [[ $x -eq 0 ]]; then # No hay proceso en la partición
            for ((j = 0; j < ${particiones[$i]}; j++)); do
                if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                    n=$(($n + 1)) # Se pasa a la siguiente línea
                    bandaMemoria[n]="     "
                    bandaMemoriaColor[n]="     "
                    numCaracteres=5
                fi
                
                for (( k = 0; k < $maxCaracteres; k++ )); do
                    bandaMemoria[n]+="*"
                    bandaMemoriaColor[n]+=$NORMAL"█\033[0m"
                done
                numCaracteres=$(($numCaracteres + $maxCaracteres))
            done
        fi

        # AÑADIR SEPARADOR DE PARTICIONES
        if [[ $i -lt ${#particiones[@]} ]]; then
            if [[ $(($numCaracteres + 1 + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaMemoria[n]="     "
                bandaMemoriaColor[n]="     "
                numCaracteres=5
            fi
            bandaMemoria[n]+="|"
            bandaMemoriaColor[n]+="|"
            numCaracteres=$(($numCaracteres + 1))
        fi
    done
    # Añadir final de banda
    memoriaespecial="0"
    for (( i = 1; i <= ${#partConProceso[@]}; i++))
    do
    if [[ ${estado[$i]} = "En ejecución" ]]
      then
        let memoriaespecial=$memoriaespecial+${memoria[$i]}
        #echo -ne "$memoriaespecial"
        #bandaMemoria[n]+="| M: $memoriaespecial"
        #bandaMemoriaColor[n]+="| M: $memoriaespecial"
    fi
    done
  
    if [[ $(($numCaracteres + 5 + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
        n=$(($n + 1)) # Se pasa a la siguiente línea
        bandaMemoria[n]="     "
        bandaMemoriaColor[n]="     "
        numCaracteres=5
    fi
    
    if [[ $memoriaespecial -eq 0 ]]
    then
      bandaMemoria[n]+="| M: 00"
      bandaMemoriaColor[n]+="| M: 00"
    else
      if [[ ${#memoriaespecial} -eq 1 ]]; then
        bandaMemoria[n]+="| M: 0${memoriaespecial}"
        bandaMemoriaColor[n]+="| M: 0${memoriaespecial}"
      else
        bandaMemoria[n]+="| M: ${memoriaespecial}"
        bandaMemoriaColor[n]+="| M: ${memoriaespecial}"
     fi
    fi

    #bandaMemoria[n]+=`printf "| M: %-$(($maxCaracteres))d" 0` # TODO: CAMBIAR NÚMERO DE MEMORIA
    #bandaMemoriaColor[n]+=`printf "| M: %-$(($maxCaracteres))d" 0` # TODO: CAMBIAR NÚMERO DE MEMORIA


    # GENERACIÓN STRING DE POSICIÓN DE MEMORIA
    local bandaPosicion=("    |")
    local bandaPosicionColor=("    |")
    local n=0 # Línea de la banda
    local numCaracteres=5
    local x=0 # Variable que indica el número de procesos que se han añadido a la banda

    for ((i = 1; i <= ${#particiones[@]}; i++)); do
        if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
            n=$(($n + 1)) # Se pasa a la siguiente línea
            bandaPosicion[n]="     "
            bandaPosicionColor[n]="     "
            numCaracteres=5
        fi
        bandaPosicion[n]+=`printf "%${maxCaracteres}d" $x`
        bandaPosicionColor[n]+=`printf "%${maxCaracteres}d" $x`
        numCaracteres=$(($numCaracteres + $maxCaracteres))

        local ultimaPosicion=-1 # Permite añadir donde se termina el proceso dentro de la memoria
        for ((j = 1; j <= ${#partConProceso[@]}; j++)); do
            if [[ $i -eq ${partConProceso[$j]} && (${estado[$j]} = "En memoria" || ${estado[$j]} = "En ejecución" || ${estado[$j]} = "En pausa") ]]; then # El proceso se puede imprimir en memoria
                ultimaPosicion=${memoria[$j]}
            fi
        done

        for ((k = 0; k < $((${particiones[$i]} - 1)); k++)); do
            if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaPosicion[n]="     "
                bandaPosicionColor[n]="     "
                numCaracteres=5
            fi
            if [[ $(($ultimaPosicion - 1)) -eq $k ]]; then
                bandaPosicion[n]+=`printf "%$(($maxCaracteres))d" $(($ultimaPosicion + $x))`
                bandaPosicionColor[n]+=`printf "%$(($maxCaracteres))d" $(($ultimaPosicion + $x))`
            else
                bandaPosicion[n]+=`printf "%$(($maxCaracteres))s" ""`
                bandaPosicionColor[n]+=`printf "%$(($maxCaracteres))s" ""`
            fi
            numCaracteres=$(($numCaracteres + $maxCaracteres))
        done

        # AÑADIR SEPARADOR DE PARTICIONES
        if [[ $i -lt ${#particiones[@]} ]]; then
            if [[ $(($numCaracteres + 1 + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaPosicion[n]="     "
                bandaPosicionColor[n]="     "
                numCaracteres=5
            fi
            bandaPosicion[n]+=" "
            bandaPosicionColor[n]+=" "
            numCaracteres=$(($numCaracteres + 1))
        fi
        x=$(($x + ${particiones[$i]}))
    done
    # Añadir final de banda
    if [[ $(($numCaracteres + 5 + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
        n=$(($n + 1)) # Se pasa a la siguiente línea
        bandaPosicion[n]="     "
        bandaPosicionColor[n]="     "
        numCaracteres=5
    fi
    bandaPosicion[n]+=`printf "|    %$(($maxCaracteres))s" ""`
    bandaPosicionColor[n]+=`printf "|    %$(($maxCaracteres))s" ""`


    # IMPRIMIR BANDAS
    for (( i = 0; i < ${#bandaProcesos[@]}; i++ )); do
        echo "${bandaProcesos[$i]}" >> ./informetemp.txt
        echo -e "${bandaProcesosColor[$i]}" | tee -a ./informeColor.txt
        echo "${bandaMemoria[$i]}" >> ./informetemp.txt
        echo -e "${bandaMemoriaColor[$i]}" | tee -a ./informeColor.txt
        echo "${bandaPosicion[$i]}" >> ./informetemp.txt
        echo -e "${bandaPosicionColor[$i]}" | tee -a ./informeColor.txt
    done
}

################################################################################################################################################################################################
# Sinopsis:   función que permite mostrar el orden de ejecución de los procesos. Se usan colores para 
#       mejor interacción con el usuario. En esta función es donde se pasan los instante de reloj
################################################################################################################################################################################################

function representacionLineaTemporal {
    
    
    for ((i = 1; i <= ${#proceso[@]}; i++)); do
	# Sumar los valores de tiempo de llegada y ejecución
	sumaParaEspacios=$((sumaParaEspacios + ${llegada[$i]} + ${tiempo[$i]}))
    done
    local maxCaracteres=0

	# Asignar un valor a maxCaracteres según la cantidad de dígitos en sumaParaEspacios
	if ((sumaParaEspacios >= 1 && sumaParaEspacios <= 99)); then
	    maxCaracteres=3
	elif ((sumaParaEspacios >= 100 && sumaParaEspacios <= 999)); then
	    maxCaracteres=4
	elif ((sumaParaEspacios >= 1000 && sumaParaEspacios <= 9999)); then
	    maxCaracteres=5
	elif ((sumaParaEspacios >= 10000 && sumaParaEspacios <= 99999)); then
	    maxCaracteres=6
	elif ((sumaParaEspacios >= 100000 && sumaParaEspacios <= 999999)); then
	    maxCaracteres=7
    	elif ((sumaParaEspacios >= 1000000 && sumaParaEspacios <= 999999)); then
	    maxCaracteres=8
    	elif ((sumaParaEspacios >= 10000000 && sumaParaEspacios <= 9999999)); then
	    maxCaracteres=9
	elif ((sumaParaEspacios >= 100000000 && sumaParaEspacios <= 99999999)); then
	    maxCaracteres=10
    	fi
    
    local terminal=$(tput cols)

    for ((s = 0; s <= ${#llegada[@]}; s++)); do
        if [[ ${estado[$s]} == "En ejecución" ]]; then
            gantt[$reloj]=$s
        fi
        if [[ ${estado[$s]} == "En espera" ]]; then
            gantt2[$reloj]=$s
        fi
    done

    echo ""

    # GENERACIÓN STRING DE PROCESOS
    local bandaProcesos=("    |")
    local bandaProcesosColor=("    |")
    local n=0 # Línea de la banda
    local numCaracteres=5

    for ((k = 0; k <= $reloj; k++)); do
        if [[ ${gantt2[$k]} -eq ${gantt2[$(($k - 1))]} ]]; then
            evento2=0
        else
            evento2=1
        fi

        if [[ ${gantt[$k]} = ${gantt[$(($k - 1))]} ]]; then # Impresión de espacios entre procesos
            evento1=0

            if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaProcesos[n]="     "
                bandaProcesosColor[n]="     "
                numCaracteres=5
            fi
            bandaProcesos[n]+=`printf "%$(($maxCaracteres))s" ""`
            bandaProcesosColor[n]+=`printf "%$(($maxCaracteres))s" ""`
            numCaracteres=$(($numCaracteres + $maxCaracteres))
            
        else # Impresión de procesos
            local p=${proceso[${gantt[$k]}]}
            evento1=1

            if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaProcesos[n]="     "
                bandaProcesosColor[n]="     "
                numCaracteres=5
            fi
            bandaProcesos[n]+=`printf "%$(($maxCaracteres))s" $p`
            bandaProcesosColor[n]+=`printf "${colores[${gantt[$k]} % 6]}%$(($maxCaracteres))s\033[0m" $p`
            numCaracteres=$(($numCaracteres + $maxCaracteres))
        fi
    done
    # Añadir final de banda
    if [[ $(($numCaracteres + 5 + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
        n=$(($n + 1)) # Se pasa a la siguiente línea
        bandaProcesos[n]="     "
        bandaProcesosColor[n]="     "
        numCaracteres=5
    fi
    bandaProcesos[n]+=`printf "|    %$(($maxCaracteres))s" ""`
    bandaProcesosColor[n]+=`printf "|    %$(($maxCaracteres))s" ""`


    # GENERACIÓN STRING DE LA LÍNEA TEMPORAL
    local bandaTiempo=(" BT |")
    local bandaTiempoColor=(" BT |")
    local n=0 # Línea de la banda
    local numCaracteres=5
    
    for ((k = 0; k <= $reloj; k++)); do
        if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
            n=$(($n + 1)) # Se pasa a la siguiente línea
            bandaTiempo[n]="     "
            bandaTiempoColor[n]="     "
            numCaracteres=5
        fi

        for (( l = 0; l < $maxCaracteres; l++ )); do
            if [[ $k -eq $reloj ]]; then
                bandaTiempo[n]+=" "
                bandaTiempoColor[n]+=" "
            else
                if [[ ${gantt[$k]} = 99 || ${gantt[$k]} = 0 ]]; then
                    bandaTiempo[n]+="-"
                    bandaTiempoColor[n]+=$NORMAL"█\033[0m"
                else
                    bandaTiempo[n]+="█"
                    bandaTiempoColor[n]+=${colores[${gantt[$k]} % 6]}"█\033[0m"
                fi
            fi
        done
        numCaracteres=$(($numCaracteres + $maxCaracteres))
    done
    # Añadir final de banda
    if [[ $(($numCaracteres + 5 + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
        n=$(($n + 1)) # Se pasa a la siguiente línea
        bandaTiempo[n]="     "
        bandaTiempoColor[n]="     "
        numCaracteres=5
    fi
    bandaTiempo[n]+=`printf "| T: %-${maxCaracteres}d" $reloj`
    bandaTiempoColor[n]+=`printf "| T: %-${maxCaracteres}d" $reloj`


    # GENERACIÓN STRING DE INSTANES DE TIEMPO
    local bandaInstantes=("    |")
    local bandaInstantesColor=("    |")
    local n=0 # Línea de la banda
    local numCaracteres=5

    for ((k = 0; k <= $reloj; k++)); do
        if [[ ${gantt[$k]} -eq ${gantt[$(($k - 1))]} ]]; then ## A partir de aqui el numero de debajo de la linea de tiempos
            if [[ $k -eq 0 || $k -eq $reloj ]]; then            
                if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                    n=$(($n + 1)) # Se pasa a la siguiente línea
                    bandaInstantes[n]="     "
                    bandaInstantesColor[n]="     "
                    numCaracteres=5
                fi
                bandaInstantes[n]+=`printf "%${maxCaracteres}d" $k`
                bandaInstantesColor[n]+=`printf "%${maxCaracteres}d" $k`
                numCaracteres=$(($numCaracteres + $maxCaracteres))
            else
                if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                    n=$(($n + 1)) # Se pasa a la siguiente línea
                    bandaInstantes[n]="     "
                    bandaInstantesColor[n]="     "
                    numCaracteres=5
                fi
                bandaInstantes[n]+=`printf "%${maxCaracteres}s" ""`
                bandaInstantesColor[n]+=`printf "%${maxCaracteres}s" ""`
                numCaracteres=$(($numCaracteres + $maxCaracteres))
            fi
        else
            if [[ $(($numCaracteres + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
                n=$(($n + 1)) # Se pasa a la siguiente línea
                bandaInstantes[n]="     "
                bandaInstantesColor[n]="     "
                numCaracteres=5
            fi
            bandaInstantes[n]+=`printf "%${maxCaracteres}d" $k`
            bandaInstantesColor[n]+=`printf "%${maxCaracteres}d" $k`
            numCaracteres=$(($numCaracteres + $maxCaracteres))
        fi
    done
    # Añadir final de banda
    if [[ $(($numCaracteres + 5 + $maxCaracteres + 1)) -gt $terminal ]]; then # El texto no cabe en la terminal
        n=$(($n + 1)) # Se pasa a la siguiente línea
        bandaInstantes[n]="     "
        bandaInstantesColor[n]="     "
        numCaracteres=5
    fi
    bandaInstantes[n]+=`printf "|    %$(($maxCaracteres))s" ""`
    bandaInstantesColor[n]+=`printf "|    %$(($maxCaracteres))s" ""`


    # IMPRIMIR BANDAS
    for (( i = 0; i < ${#bandaProcesos[@]}; i++ )); do
        echo "${bandaProcesos[$i]}" >> $informeSinColor
        echo -e "${bandaProcesosColor[$i]}" | tee -a $informeConColor
        echo "${bandaTiempo[$i]}" >> $informeSinColor
        echo -e "${bandaTiempoColor[$i]}" | tee -a $informeConColor
        echo "${bandaInstantes[$i]}" >> $informeSinColor
        echo -e "${bandaInstantesColor[$i]}" | tee -a $informeConColor
    done
    echo >>$informeSinColor
    echo >>$informeSinColor
    echo >>$informeSinColor
    echo >>$informeConColor
    echo >>$informeConColor
    echo >>$informeConColor
    # Aquí van pasando los instantes de reloj para todo el algoritmo
    if [[ ${gantt[$k]} = ${gantt[$(($k - 1))]} ]]; then
        evento1=0
    else
        evento1=1
    fi
    if [[ ${gantt2[$k]} = ${gantt2[$(($k - 1))]} ]]; then
        evento2=0
    else
        evento2=1
    fi

    # SIGUIENTE IMPRESIÓN
    case $optejecucion in
    1) # Ejecución automatica.
        if [[ $evento1 -eq 1 ]]; then
            echo ""
        else
            if [[ $evento2 -eq 1 ]]; then
                echo ""
            else
                if [[ $evento3 -eq 1 ]]; then
                    echo ""
                fi
            fi
        fi
        clear
        return;;
    2) # Ejecución manual.
        if [[ $evento1 -eq 1 ]]; then
            echo -ne $ROJO"\n\n Pulsa ENTER para continuar "$NORMAL
            cat informeColor.txt >> informeColorSRPT.txt
            cat informetemp.txt > $informeSinColor
            read enterContinuar
        else
            if [[ $evento2 -eq 1 ]]; then
                echo -ne $ROJO"\n\n Pulsa ENTER para continuar "$NORMAL
                cat informeColor.txt >> informeColorSRPT.txt
                cat informetemp.txt > $informeSinColor
                read enterContinuar
            else
                if [[ $evento3 -eq 1 ]]; then
                    echo -ne $ROJO"\n\n Pulsa ENTER para continuar "$NORMAL
                    cat informeColor.txt >> informeColorSRPT.txt
                    cat informetemp.txt > $informeSinColor
                    read enterContinuar
                fi
            fi
        fi
        clear
        return;;
    3) # Ejecución por tiempo
        if [[ $evento1 == 1 ]]; then
            sleep $tiempoejecucion
        else
            if [[ $evento2 == 1 ]]; then
                sleep $tiempoejecucion
            else
                if [[ $evento3 == 1 ]]; then
                    sleep $tiempoejecucion
                fi
            fi
        fi
        clear
        return;;
    *)
        echo " Opcion incorrecta"
        clear
        return;;
    esac
}

evento1=0
evento2=0
evento3=0

################################################################################################################################################################################################
# Sinopsis:   muestra en pantalla/informe una tabla con el resultado final tras la ejecución de todos los procesos
#
################################################################################################################################################################################################

function resultadoFinalDeLaEjecucion {
    echo "" >> $informeConColor
    echo "" >> $informeSinColor
    echo "" >> $informeConColor
    echo "" >>$informeSinColor
    echo -e $AMARILLO" RESULTADO FINAL DE LA EJECUCIÓN DE PROCESOS:"$NORMAL | tee -a $informeConColor
    echo " RESULTADO FINAL DE LA EJECUCIÓN DE PROCESOS: " >>$informeSinColor
    echo -e " Ref Tll Tej Mem Tesp Tret Trej Part Estado" | tee -a $informeConColor
    echo " Ref Tll Tej Mem Tesp Tret Trej Part Estado" >> $informeSinColor

    for ((i = 1; i <= ${#tiempo[@]}; i++)); do

        echo -ne " ${colores[$i % 6]}${proceso[$i]}" | tee -a $informeConColor
        echo -ne " ${proceso[$i]}" >>$informeSinColor
        if [[ ${llegada[$i]} -le 9 ]]; then #Si es menor o igual que 9
            echo -ne "   ${colores[$i % 6]}${llegada[$i]}" | tee -a $informeConColor
            echo -ne "   ${llegada[$i]}" >>$informeSinColor
        else
            echo -ne "  ${colores[$i % 6]}${llegada[$i]}" | tee -a $informeConColor
            echo -ne "  ${llegada[$i]}" >>$informeSinColor
        fi
        if [[ ${tiempo[$i]} -le 9 ]]; then #Si es menor o igual que 9
            echo -ne "   ${colores[$i % 6]}${tiempo[$i]}" | tee -a $informeConColor
            echo -ne "  ${tiempo[$i]}" >>$informeSinColor
        else
            echo -ne "  ${colores[$i % 6]}${tiempo[$i]}" | tee -a $informeConColor
            echo -ne "  ${tiempo[$i]}" >>$informeSinColor
        fi
        if [[ ${memoria[$i]} -le 9 ]]; then #Si es menor o igual que 9
            echo -ne "   ${colores[$i % 6]}${memoria[$i]}" | tee -a $informeConColor
            echo -ne "   ${memoria[$i]}" >>$informeSinColor
        else
            echo -ne "  ${colores[$i % 6]}${memoria[$i]}" | tee -a $informeConColor
            echo -ne "  ${memoria[$i]}" >>$informeSinColor
        fi
        if [[ ${tiempNEsperaProceso[$i]} -le 9 ]]; then #Si es menor o igual que 9
            echo -ne "    ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a $informeConColor
            echo -ne "    ${tiempNEsperaProceso[$i]}" >>$informeSinColor
        else
            echo -ne "   ${colores[$i % 6]}${tiempNEsperaProceso[$i]}" | tee -a $informeConColor
            echo -ne "   ${tiempNEsperaProceso[$i]}" >>$informeSinColor
        fi
        if [[ ${tiempoNRespuProceso[$i]} -le 9 ]]; then #Si es menor o igual que 9
            echo -ne "    ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a $informeConColor
            echo -ne "    ${tiempoNRespuProceso[$i]} " >>$informeSinColor
        else
            echo -ne "   ${colores[$i % 6]}${tiempoNRespuProceso[$i]} " | tee -a $informeConColor
            echo -ne "   ${tiempoNRespuProceso[$i]} " >>$informeSinColor
        fi
        if [[ ${restante[$i]} -le 0 ]]; then
            echo -ne "   ${colores[$i % 6]}0 " | tee -a $informeConColor
            echo -ne "   0 " >>$informeSinColor
        elif [[ ${restante[$i]} -le 9 ]]; then #Si es menor o igual que 9
            echo -ne "   ${colores[$i % 6]}${restante[$i]} " | tee -a $informeConColor
            echo -ne "   ${restante[$i]} " >>$informeSinColor
        else
            echo -ne "    ${colores[$i % 6]}${restante[$i]} " | tee -a $informeConColor
            echo -ne "     ${restante[$i]} " >>$informeSinColor
        fi

        if [[ ("${estado[$i]}" == "Fuera de la CPU" || "${estado[$i]}" == "Finalizado") ]]; then
            echo -ne "   ${colores[$i % 6]}- " | tee -a $informeConColor
            echo -ne "   - " >>$informeSinColor
        elif [[ ${partConProceso[$i]} -le 9 ]]; then
            echo -ne "   ${colores[$i % 6]}${partConProceso[$i]} " | tee -a $informeConColor
            echo -ne "   ${partConProceso[$i]} " >>$informeSinColor
        else
            echo -ne "  ${colores[$i % 6]}${partConProceso[$i]} " | tee -a $informeConColor
            echo -ne "  ${partConProceso[$i]} " >>$informeSinColor
        fi
        echo -ne "${colores[$i % 6]}${estado[$i]} " | tee -a $informeConColor
        echo -ne "${estado[$i]} " >>$informeSinColor
        echo -e "" | tee -a $informeConColor
        echo -e "" >>$informeSinColor

    done
    echo "" | tee -a $informeConColor
    echo "" >>$informeSinColor
    echo -en $AMARILLO" TIEMPO DE ESPERA Y RESPUESTA:"$NORMAL | tee -a $informeConColor
    echo "" | tee -a $informeConColor
    echo -e " TIEMPO DE ESPERA Y RESPUESTA:" >>$informeSinColor
    echo "" >>$informeSinColor
    echo -e " Tiempo medio de Espera: $promedio_espera,$promedio_esperad\tTiempo medio de Retorno: $promedio_respuesta,$promedio_respuestad" | tee -a $informeConColor
    echo -e " Tiempo medio de Espera: $promedio_espera,$promedio_esperad\tTiempo medio de Retorno: $promedio_respuesta,$promedio_respuestad" >>$informeSinColor
    echo -ne $ROJO"\n\n Pulsa ENTER para continuar "$NORMAL
    read enterContinuar
}

################################################################################################################################################################################################
# Sinopsis:   función que calcula de los promedios de espera y de respuesta
################################################################################################################################################################################################

function calcularPromediosEsperaRespuesta {
    suma_espera=0
    suma_respuesta=0
    counter=0
    for ((ss = 1; ss <= ${#llegada[@]}; ss++)); do
        if [[ ${procesoEnParticionOcupada[$ss]} -eq 1 || ${estado[$ss]} != "Fuera del sistema" ]]; then
            let suma_espera=$(expr ${tiempoEsperaProceso[$ss]} + $suma_espera)
            let suma_respuesta=$(expr ${tiempoRespuestaProceso[$ss]} + $suma_respuesta)
        fi
        if [[ ${estado[$ss]} != "Fuera del sistema" ]]; then
            let counter=$counter+1
        fi
    done
    if [[ $counter -ne 0 ]]; then
        promedio_espera=$(expr $suma_espera / $counter)
        let promedio_esperad=$suma_espera*100/$counter-$promedio_espera*100
        promedio_respuesta=$(expr $suma_respuesta / $counter)
        let promedio_respuestad=$suma_respuesta*100/$counter-$promedio_respuesta*100

        echo -ne $NORMAL" Tiempo medio de Espera: $promedio_espera,$promedio_esperad\tTiempo medio de Retorno: $promedio_respuesta,$promedio_respuestad" | tee -a ./informeColor.txt
        echo -e " Tiempo medio de Espera: $promedio_espera,$promedio_esperad\tTiempo medio de Retorno: $promedio_respuesta,$promedio_respuestad" >>./informetemp.txt
        echo "" | tee -a ./informeColor.txt
        echo "" >>./informetemp.txt
    else
        echo -ne $NORMAL" Tiempo medio de Espera: 0,0\tTiempo medio de Retorno: 0,0" | tee -a ./informeColor.txt
        echo -e " Tiempo medio de Espera: 0,0\tTiempo medio de Retorno: 0,0" >>./informetemp.txt
        echo "" | tee -a ./informeColor.txt
        echo "" >>./informetemp.txt
    fi
}

################################################################################################################################################################################################
# Sinopsis:   permite al usuario ver, o no, un informe (que se ha creado de todas maneras)
################################################################################################################################################################################################

function mostrarInforme {
    clear
    echo -e $AMARILLO"\nSE HA GENERADO UN INFORME"$NORMAL
    echo -e "\n1. Ver informe a color en pantalla (se usa 'more')"
    echo -e "\n2. Ver informe en blanco y negro en 'gedit'"
    echo -e "\n3. Salir"
    echo -n -e "\n--> "
    read numero

    #Comprobación de que el número introducido por el usuario es 1, 2 ó 3
    while [[ 1 -lt $numero || $numero -lt 3 ]]; do
        case "$numero" in
        '1')
            more $informeConColor
            break
            ;;

        '2')
            gedit $informeSinColor
            break
            ;;

        '3')
            echo -e $ROJO"\nSE HA SALIDO DEL PROGRAMA"$NORMAL
            exit 0
            break
            ;;

        *)
            clear
            echo -e $AMARILLO"\nMENÚ INICIO" $NORMAL
            echo -e "\n1. Ver manual de usuario (requiere 'evince')"
            echo -e "\n2. Acceder al programa principal"
            echo -e "\n3. Salir"
            echo -n -e "\n--> "
            read numero
            ;;
        esac
    done
}

############################################################################################################
# PROGRAMA PRINCIPAL
############################################################################################################

#Llamada a todas las funciones de forma secuencial
presentacionPantallaInforme
menuInicio
inicializaVectores
if [ "$algoritmoE" -eq 1 ]; then
    algoritmoFCFS_AjustePrimer
elif [ "$algoritmoE" -eq 2 ]; then
    algoritmoSJF_AjustePrimer
elif [ "$algoritmoE" -eq 3 ]; then
    algoritmoSRPT_AjustePrimer
fi
resultadoFinalDeLaEjecucion
mostrarInforme
